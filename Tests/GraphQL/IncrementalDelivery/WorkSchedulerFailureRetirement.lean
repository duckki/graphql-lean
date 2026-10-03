import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation

/-! Failed-owner retirement alone does not prove health of retained descendant shells. -/

namespace GraphQL.IncrementalDelivery.Tests.WorkSchedulerFailureRetirement
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

private def parent : DeliveryNode := { ref := 0, path := [] }
private def child : DeliveryNode := { ref := 1, path := [] }
private def failedTask : Occurrence := .executionGroup [0]

private def work : Execution.Work :=
  .combine
    (.executionGroup [⟨parent, []⟩] [] (.error 1) .empty)
    (.executionGroup [⟨child, [parent]⟩] [] (.ok ([], 0)) .empty)

private def childNode : GroupNode :=
  { group := ⟨child, some parent.ref⟩, tasks := [.executionGroup [1]], pending := 1 }

private def queue : State :=
  { registeredGroups := [parent.ref, child.ref], groupNodes := [childNode] }

/-- The raw fixture's failed task directly owns only the parent group.
Witness: evaluate its fixed work occurrence; no execution-generation claim is made. -/
private theorem failed_known
    : TaskAt work failedTask [parent.ref] none (.object [] (.error 1)) := by
  exact ⟨[⟨parent, []⟩], [], _, .empty, [], rfl, rfl, rfl⟩

/-- Every direct owner of the recorded failure is retired in this deliberately raw queue.
Witness: task-descriptor uniqueness fixes the owner list, and the parent is registered
but absent. This is not asserted to be a complete reachable-state invariant. -/
theorem failed_owners_retired
    : ∀ occurrence ∈ [failedTask],
        ∀ owners,
          TaskHasOwners work occurrence owners
          → ∀ ref ∈ owners, queue.RetiredGroup ref := by
  intro occurrence member owners known ref owner
  have same := List.mem_singleton.mp member
  subst occurrence
  obtain ⟨producer, payload, descriptor⟩ := known
  have ownersEq := (TaskAt.unique descriptor failed_known).1
  rw [ownersEq] at owner
  have sameRef := List.mem_singleton.mp owner
  subst ref
  exact State.RetiredGroup.of_lookup_none (by decide) (by cbv)

/-- Retirement does not remove an arbitrary retained child's invalid ancestor.
Witness: the actual dependency rule propagates the parent's recorded task failure. -/
theorem child_invalidated : GroupInvalidated work [failedTask] child.ref := by
  have known : NodeAt work child .group [parent.ref] none := by
    exact ⟨[1], [⟨child, [parent]⟩], [], .ok ([], 0), .empty, [],
      ⟨child, [parent]⟩, rfl, List.mem_cons_self, rfl, rfl⟩
  exact .groupDependency ⟨child, none, known, rfl⟩ List.mem_cons_self
    (.task ⟨none, _, failed_known⟩ List.mem_cons_self List.mem_cons_self)

/-- The invalidated child is genuinely live but unannounced in the raw fixture.
Witness: direct lookup and empty roots; this guards against treating retirement as a
proof that every live group is healthy without the missing ancestry/replay argument. -/
theorem live_unhealthy_shell
    : queue.groupNode? child.ref = some childNode
      ∧ queue.rootGroups = []
      ∧ GroupInvalidated work [failedTask] child.ref :=
  ⟨by cbv, rfl, child_invalidated⟩

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerFailureRetirement
