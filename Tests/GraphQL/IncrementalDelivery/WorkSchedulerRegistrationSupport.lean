import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RegistrationProvenance
import Tests.GraphQL.IncrementalDelivery.Fixtures.WorkDeclarations

open GraphQL.IncrementalDelivery.Tests (declaredTask)

namespace GraphQL.IncrementalDelivery.Tests.WorkSchedulerRegistrationSupport
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

private def ancestor : DeliveryNode := ⟨0, [], none⟩
private def child : DeliveryNode := ⟨1, [], none⟩

private def work : Execution.Work :=
  declaredTask [⟨child, [ancestor]⟩] [] ({ result := .ok ([], 0) }) .empty

private def queue : State := State.initialize (Work.fromExecution work)

private def event : GraphEvent :=
  .taskSuccess (.executionGroup [])
    { value := { path := [], data := [], errors := 0, deliveryGroups := [child] } }

private def supported (ref : NodeRef) : Prop :=
  ∃ task ∈ queue.tasks, task.SupportsGroup work ref

/-- This raw contributor's full chain supports both permanent registrations. -/
theorem initial_support : queue.RegistrationsSatisfy supported := by
  intro ref member
  have registered : queue.registeredGroups = [ancestor.ref, child.ref] := by rfl
  rw [registered] at member
  refine ⟨
    ⟨.executionGroup [], [child]⟩,
    by
      change _ ∈ ([⟨.executionGroup [], [child]⟩] : List Task)
      exact List.mem_cons_self,
    [],
    [⟨child, [ancestor]⟩],
    [],
    { result := .ok ([], 0) },
    .empty,
    none,
    [],
    ⟨child, [ancestor]⟩,
    rfl,
    ?_,
    List.mem_cons_self,
    ?_
  ⟩
  · rfl
  · simpa [List.mem_cons, or_comm] using member

/-- Permanent registration does not imply a directly contributing task.
Witness: the ancestor is registered, but the sole task's contributor list is just C.
-/
theorem not_directly_owned
    : ¬∀ ref ∈ queue.registeredGroups,
        ∃ task ∈ queue.tasks, ref ∈ task.groups.map DeliveryNode.ref := by
  intro all
  have registered : ancestor.ref ∈ queue.registeredGroups := by
    cbv
    exact List.mem_cons_self
  obtain ⟨task, member, contributes⟩ := all ancestor.ref registered
  have tasks : queue.tasks = [⟨.executionGroup [], [child]⟩] := by cbv
  rw [tasks] at member
  have same := List.mem_singleton.mp member
  subst task
  simp [ancestor, child] at contributes

/-- The successful task is a legal, fresh, producer-ready source event.
Witness: the root task's fixed payload and empty child work.
-/
theorem valid_input : ValidGraphEvents work [event] := by
  have task : TaskAt work (.executionGroup []) [child.ref] none (.object [] (.ok ([], 0))) :=
    ⟨_, _, _, _, [], rfl, rfl, rfl⟩
  exact .append .nil ⟨_, _, task, rfl, rfl⟩
    (by simp [GraphEvent.Fresh, GraphEvent.identities, event])
    ⟨_, _, _, task, by intro source impossible; cases impossible⟩

/-- Source replay retains support even after every live group and task node is gone.
Witness: this fixture retains its permanent registry and supporting task descriptor
through the matching success, which also terminates the queue.
-/
theorem completed_support
    : (queue.runNormalized [[event]]).1.RegistrationsSatisfy supported
      ∧ (queue.runNormalized [[event]]).1.terminated = true
      ∧ (queue.runNormalized [[event]]).1.groupNodes = [] := by
  exact ⟨initial_support, by cbv, by cbv⟩

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerRegistrationSupport
