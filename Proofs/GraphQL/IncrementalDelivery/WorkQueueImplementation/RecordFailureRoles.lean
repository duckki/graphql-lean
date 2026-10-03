import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RecordInvalidation

/-! Stream failures cannot invalidate defer registration records through cleanup alone. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics
open GraphQL.IncrementalDelivery.Semantics

-----------------------------------------------------------------------------------------
-- Execution assigns defer roles to every registration record and all of its ancestors
-----------------------------------------------------------------------------------------

/-- Generated work has one role assignment for stream nodes and all defer metadata.
Witness: execution's allocation induction, including taskless ancestor descriptors.
-/
theorem ExecutedWork.refRoles {work : Execution.Work} (generated : ExecutedWork work)
    : ∃ roles, RefRoles.WorkRoles roles work := by
  obtain ⟨ObjectRef, schema, resolvers, variables, fuel, parentType, source,
    selections, same⟩ := generated
  obtain ⟨roles, assigned⟩ := RefRoles.executeRoot_roles schema resolvers variables fuel
    parentType source selections 0
  exact ⟨roles, same ▸ assigned⟩

/-- A registration chain contains only defer refs, even when no task owns its head.
Witness: its located contributor metadata and the recorded ancestor suffix.
-/
private theorem groupRecord_roles {work roles node dependencies}
    (assigned : RefRoles.WorkRoles roles work)
    (record : GroupRecordAt work node dependencies)
    : roles node.ref = false ∧ ∀ ref ∈ dependencies, roles ref = false := by
  obtain ⟨address, groups, path, result, children, producer, owners, fragment,
    ancestors, located, member, suffix, rfl⟩ := record
  have localWork := generatedWorkRoles_located assigned
    (StructuralEquivalence.located_of_current located)
  simp only [RefRoles.WorkRoles] at localWork
  have groupRoles := localWork.1 fragment member
  have atNode (entry : Execution.DeliveryNode) (included : entry ∈ node :: ancestors)
      : roles entry.ref = false := by
    rcases List.mem_cons.mp (suffix.subset included) with same | ancestor
    · exact same ▸ groupRoles.1
    · exact groupRoles.2 entry ancestor
  refine ⟨atNode node List.mem_cons_self, ?_⟩
  intro ref included
  obtain ⟨ancestor, member, rfl⟩ := List.mem_map.mp included
  exact atNode ancestor (List.mem_cons_of_mem _ member)

/-- Removing failed items cannot remove a defer record's cleanup cause.
Witness: induct over cleanup with execution's role assignment. A direct item cause
would require a stream ref to be a defer ref; ancestor steps retain their defer roles.
`retained` preserves object failures only, not every failure in the mixed inventory.
This concerns cleanup, not the scheduler's additional producer/stream causal rules.
-/
theorem GroupRecordInvalidated.restrict_objectFailures
    {work failed kept node dependencies} (generated : ExecutedWork work)
    (record : GroupRecordAt work node dependencies)
    (invalid : GroupRecordInvalidated work failed node.ref)
    (retained
      : ∀ occurrence owners producer path result,
          TaskAt work occurrence owners producer (.object path result)
          → occurrence ∈ failed
          → occurrence ∈ kept)
    : GroupRecordInvalidated work kept node.ref := by
  obtain ⟨roles, assigned⟩ := generated.refRoles
  have restrict {ref} (failure : GroupRecordInvalidated work failed ref)
      (groupRole : roles ref = false)
      : GroupRecordInvalidated work kept ref := by
    induction failure with
    | task known owner member =>
        obtain ⟨producer, payload, task⟩ := known
        cases StructuralEquivalence.taskAt_of_current task with
        | executionGroup located =>
            exact .task ⟨_, _, .executionGroup located.toCurrent⟩ owner
              (retained _ _ _ _ _ (.executionGroup located.toCurrent) member)
        | item located selected =>
            have localWork := generatedWorkRoles_located assigned located
            simp only [RefRoles.WorkRoles] at localWork
            have streamRole := localWork.1
            have same := List.mem_singleton.mp owner
            rw [← same, groupRole] at streamRole
            cases streamRole
    | ancestor descriptor member _ ih =>
        exact .ancestor descriptor member
          (ih ((groupRecord_roles assigned descriptor).2 _ member))
  exact restrict invalid (groupRecord_roles assigned record).1

/-- Defer-record cleanup is unchanged when a mixed inventory drops only item failures.
Witness: the role-aware restriction above and monotonicity for the retained sublist.
Neither ordering nor failure licensing is assumed by this accounting equivalence.
-/
theorem ExecutedWork.groupRecordInvalidated_iff_objectFailures
    {work failed kept node dependencies} (generated : ExecutedWork work)
    (record : GroupRecordAt work node dependencies) (included : kept.Subset failed)
    (retained
      : ∀ occurrence owners producer path result,
          TaskAt work occurrence owners producer (.object path result)
          → occurrence ∈ failed
          → occurrence ∈ kept)
    : GroupRecordInvalidated work failed node.ref
      ↔ GroupRecordInvalidated work kept node.ref :=
  ⟨
    fun invalid => invalid.restrict_objectFailures generated record retained,
    fun invalid => invalid.mono included
  ⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
