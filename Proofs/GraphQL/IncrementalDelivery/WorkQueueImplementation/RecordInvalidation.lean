import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupInvalidation

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Cleanup follows registration records, including taskless ancestor wrappers
-----------------------------------------------------------------------------------------

/-- A failed task invalidates its contributors and their descendant registration records.
`failed` lists settled task failures; `key` may name a taskless ancestor record. This is
proof-side cleanup evidence, not a new scheduler event or a claim of task ownership.
-/
inductive GroupRecordInvalidated (work : Execution.Work) (failed : List Occurrence)
    : Nat → Prop
  | task {occurrence owners key}
    (known : TaskHasOwners work occurrence owners)
    (owner : key ∈ owners) (member : occurrence ∈ failed)
    : GroupRecordInvalidated work failed key
  | ancestor {node dependencies key}
    (known : GroupRecordAt work node dependencies) (member : key ∈ dependencies)
    (failure : GroupRecordInvalidated work failed key)
    : GroupRecordInvalidated work failed node.key

/-- Cleanup evidence persists when more failed tasks are recorded.
Witness: induction over direct contribution and registration ancestry.
-/
theorem GroupRecordInvalidated.mono {work before after key}
    (failure : GroupRecordInvalidated work before key) (included : before.Subset after)
    : GroupRecordInvalidated work after key := by
  induction failure with
  | task known owner member => exact .task known owner (included member)
  | ancestor known member _ ih => exact .ancestor known member ih

/-- Registration cleanup still requires a settled task failure somewhere in its cause.
Witness: follow the ancestry derivation to its failed contributing task.
-/
theorem GroupRecordInvalidated.nonempty {work failed key}
    (failure : GroupRecordInvalidated work failed key)
    : failed ≠ [] := by
  induction failure with
  | task _ _ member => intro empty; simp [empty] at member
  | ancestor _ _ _ ih => exact ih

/-- Contributor-only invalidation also explains registration-record cleanup.
Witness: every actual group descriptor supplies its corresponding registration record.
-/
theorem GroupInvalidated.toRecordInvalidated {work failed key}
    (failure : GroupInvalidated work failed key)
    : GroupRecordInvalidated work failed key := by
  induction failure with
  | task known owner member => exact .task known owner member
  | groupDependency known member _ ih =>
      obtain ⟨node, producer, descriptor, same⟩ := known
      exact same ▸ .ancestor (groupRecordAt_of_nodeAt descriptor) member ih

-----------------------------------------------------------------------------------------
-- On generated contributors, record cleanup has exactly the original causal meaning
-----------------------------------------------------------------------------------------

/-- Record invalidation is direct or comes from the record's own complete ancestry.
Witness: generated canonical dependencies identify the ancestry rule's descriptor.
Unlike contributor decomposition, this also applies to taskless intermediate records.
-/
theorem ExecutedWork.groupRecordInvalidated_causes {work : Execution.Work}
    (generated : ExecutedWork work) {node dependencies failed}
    (known : GroupRecordAt work node dependencies)
    (failure : GroupRecordInvalidated work failed node.key)
    : (∃ occurrence owners,
        TaskHasOwners work occurrence owners ∧ node.key ∈ owners ∧ occurrence ∈ failed)
      ∨ ∃ dependency ∈ dependencies, GroupRecordInvalidated work failed dependency := by
  generalize keyEq : node.key = key at failure
  cases failure with
  | task task owner member => exact .inl ⟨_, _, task, keyEq.symm ▸ owner, member⟩
  | @ancestor other otherDependencies key descriptor member prior =>
      obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
      have same : otherDependencies = dependencies := by
        rw [canonical other otherDependencies descriptor,
          canonical node dependencies known, keyEq]
      exact .inr ⟨key, same ▸ member, prior⟩

/-- Full generated ancestry remains transitive through taskless registration records.
Witness: project both records into execution's bounded canonical ancestor assignment.
-/
theorem ExecutedWork.groupRecordAncestors_trans
    {work : Execution.Work} (generated : ExecutedWork work)
    {node ancestor dependencies ancestorDependencies}
    (known : GroupRecordAt work node dependencies)
    (ancestorKnown : GroupRecordAt work ancestor ancestorDependencies)
    (member : ancestor.key ∈ dependencies)
    : ancestorDependencies.Subset dependencies := by
  obtain ⟨parents, bound, valid, canonical⟩ := generated.groupRecordsValid
  obtain ⟨keyBound, dependenciesEq⟩ := canonical node dependencies known
  have ancestorEq := (canonical ancestor ancestorDependencies ancestorKnown).2
  rw [dependenciesEq] at member ⊢
  rw [ancestorEq]
  exact (valid.1 node.key keyBound ancestor.key member).2

/-- Recursive record cleanup has one failed contributing task as its origin.
Witness: flatten intermediate registration records using generated ancestry transitivity.
-/
private theorem GroupRecordInvalidated.origin {work failed key}
    (failure : GroupRecordInvalidated work failed key) (generated : ExecutedWork work)
    : ∃ occurrence owners owner,
        TaskHasOwners work occurrence owners
        ∧ occurrence ∈ failed
        ∧ owner ∈ owners
        ∧ (owner = key
            ∨ ∃ node dependencies,
                GroupRecordAt work node dependencies
                ∧ node.key = key
                ∧ owner ∈ dependencies) := by
  induction failure with
  | @task occurrence owners key known owner member =>
      exact ⟨occurrence, owners, key, known, member, owner, .inl rfl⟩
  | @ancestor node dependencies key known member _ ih =>
      obtain ⟨occurrence, owners, owner, task, recorded, contributes,
        direct | earlier⟩ := ih
      · exact ⟨occurrence, owners, owner, task, recorded, contributes,
          .inr ⟨node, dependencies, known, rfl, direct ▸ member⟩⟩
      · obtain ⟨ancestor, ancestorDependencies, ancestorKnown, ancestorKey,
          inAncestors⟩ := earlier
        have included := generated.groupRecordAncestors_trans known ancestorKnown
          (ancestorKey.symm ▸ member)
        exact ⟨occurrence, owners, owner, task, recorded, contributes,
          .inr ⟨node, dependencies, known, rfl, included inAncestors⟩⟩

/-- A generated record is invalidated exactly by a failed owner in its full chain.
Witness: the flattened origin and canonical record ancestry; conversely use the direct
task rule or a single ancestry step.
-/
theorem ExecutedWork.groupRecordInvalidated_iff
    {work : Execution.Work} (generated : ExecutedWork work) {node dependencies failed}
    (known : GroupRecordAt work node dependencies)
    : GroupRecordInvalidated work failed node.key
      ↔ ∃ occurrence owners owner,
          TaskHasOwners work occurrence owners
          ∧ occurrence ∈ failed
          ∧ owner ∈ owners
          ∧ owner ∈ node.key :: dependencies := by
  constructor
  · intro failure
    obtain ⟨occurrence, owners, owner, task, recorded, contributes,
      direct | ancestor⟩ := failure.origin generated
    · exact ⟨occurrence, owners, owner, task, recorded, contributes, by simp [direct]⟩
    · obtain ⟨other, otherDependencies, otherKnown, sameKey, member⟩ := ancestor
      obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
      have same : otherDependencies = dependencies := by
        rw [canonical other otherDependencies otherKnown,
          canonical node dependencies known, sameKey]
      exact ⟨occurrence, owners, owner, task, recorded, contributes,
        List.mem_cons.mpr (.inr (same ▸ member))⟩
  · rintro ⟨occurrence, owners, owner, task, recorded, contributes, member⟩
    have direct : GroupRecordInvalidated work failed owner :=
      .task task contributes recorded
    rcases List.mem_cons.mp member with same | ancestor
    · exact same ▸ direct
    · exact .ancestor known ancestor direct

/-- Record cleanup agrees with the original causal invalidation on actual contributors.
Witness: both generated-work characterizations have the same failed-owner condition.
Taskless records do not acquire fictitious task or observable-node descriptors.
-/
theorem ExecutedWork.groupRecordInvalidated_iff_groupInvalidated
    {work : Execution.Work} (generated : ExecutedWork work)
    {node dependencies producer failed}
    (known : NodeAt work node .group dependencies producer)
    : GroupRecordInvalidated work failed node.key
      ↔ GroupInvalidated work failed node.key :=
  (generated.groupRecordInvalidated_iff (groupRecordAt_of_nodeAt known)).trans
    (generated.groupInvalidated_iff known).symm

/-- Cleanup of an actual generated group retains its historical scheduler cause.
Witness: contributor equivalence followed by the existing explained-history bridge.
-/
theorem GroupRecordInvalidated.toNodeFailed
    {work failed node dependencies producer groups streams events matching cuts}
    (failure : GroupRecordInvalidated work failed node.key)
    (generated : ExecutedWork work)
    (known : NodeAt work node .group dependencies producer)
    (explained : Explains work groups streams events matching cuts)
    (included : failed.Subset (failedBefore cuts events.length))
    : NodeFailed work matching events cuts node.key :=
  ((generated.groupRecordInvalidated_iff_groupInvalidated known).mp failure).toNodeFailed
    explained included

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
