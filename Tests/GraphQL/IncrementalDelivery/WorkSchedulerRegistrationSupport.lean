import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RegistrationProvenance

namespace GraphQL.IncrementalDelivery.Tests.WorkSchedulerRegistrationSupport
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

private def ancestor : DeliveryNode := ⟨0, [], none⟩
private def child : DeliveryNode := ⟨1, [], none⟩

private def work : Execution.Work :=
  .executionGroup [⟨child, [ancestor]⟩] [] (.ok ([], 0)) .empty

private def queue : State := State.initialize (Work.fromExecution work)

private def event : GraphEvent :=
  .taskSuccess (.executionGroup [])
    { value := { path := [], data := [], errors := 0, deliveryGroups := [child] } }

/-- Initialization retains task support for the taskless ancestor after pruning it.
Witness: the general full-chain initialization theorem, not direct ownership.
-/
theorem initial_support : queue.RegistrationsSupportedBy (Task.SupportsGroup work) :=
  createWorkQueue_fromSpec_registrationsSupported work

/-- Permanent registration does not imply a directly contributing task.
Witness: the ancestor is registered, but the sole task's contributor list is just C.
-/
theorem not_directly_owned : ¬queue.RegistrationsHaveTasks := by
  intro all
  have registered : ancestor.key ∈ queue.registeredGroups := by
    cbv
    exact List.mem_cons_self
  obtain ⟨task, member, contributes⟩ := all ancestor.key registered
  have tasks : queue.tasks = [⟨.executionGroup [], [child]⟩] := by cbv
  rw [tasks] at member
  have same := List.mem_singleton.mp member
  subst task
  simp [ancestor, child] at contributes

/-- The successful task is a legal, fresh, producer-ready source event.
Witness: the root task's fixed payload and empty child work.
-/
theorem valid_input : ValidGraphEvents work [event] := by
  have task : TaskAt work (.executionGroup []) [child.key] none (.object [] (.ok ([], 0))) :=
    ⟨_, _, _, _, [], rfl, rfl, rfl⟩
  exact .append .nil ⟨_, _, task, rfl, rfl⟩
    (by simp [GraphEvent.Fresh, GraphEvent.identities, event])
    ⟨_, _, _, task, by intro source impossible; cases impossible⟩

/-- Source replay retains support even after every live group and task node is gone.
Witness: the unconditional valid-replay provenance theorem and concrete termination.
-/
theorem completed_support
    : (queue.runNormalized [[event]]).1.RegistrationsSupportedBy (Task.SupportsGroup work)
      ∧ (queue.runNormalized [[event]]).1.terminated = true
      ∧ (queue.runNormalized [[event]]).1.groupNodes = [] := by
  exact ⟨createWorkQueue_runNormalized_registrationsSupported valid_input, by cbv, by cbv⟩

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerRegistrationSupport
