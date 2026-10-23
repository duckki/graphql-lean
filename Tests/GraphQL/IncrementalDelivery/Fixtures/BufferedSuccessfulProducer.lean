import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SourceRegistrationAccounting
import Tests.GraphQL.IncrementalDelivery.Fixtures.WorkDeclarations

open GraphQL.IncrementalDelivery.Tests (declaredTask)

/-! An admitted buffered success can be ignored after its shared owner is cancelled. -/

namespace GraphQL.IncrementalDelivery.Tests.BufferedSuccessfulProducer
open GraphQL.IncrementalDelivery
open GraphQL.IncrementalDelivery.Execution
open ReferenceWorkQueue WorkQueueSemantics

private def owner : DeliveryNode := ⟨0, [], none⟩
private def child : DeliveryNode := ⟨1, [], none⟩
private def producer : Occurrence := .executionGroup [0]
private def failure : Occurrence := .executionGroup [1]
private def nested : Occurrence := .executionGroup [0, 0]

private def value : ExecutionGroupValue :=
  { path := [], data := [("a", .scalar "a")], errors := 0, deliveryGroups := [owner] }

private def children : Execution.Work :=
  declaredTask [⟨child, []⟩] [] { result := .ok ([("b", .scalar "b")], 0) } .empty

private def work : Execution.Work :=
  .combine (declaredTask [⟨owner, []⟩] [] { result := .ok (value.data, 0) } children)
    (declaredTask [⟨owner, []⟩] [] { result := .error 1, cause := some 1 } .empty)

private def initial : ReferenceWorkQueue.State := .initialize (.fromExecution work)

private def success : GraphEvent :=
  .taskSuccess producer ⟨value, .fromExecution children [0, 0]⟩

private def batch : List GraphEvent := [.taskFailure failure 1, success]

/-- Both source outcomes match their tasks, and neither task has a structural producer. -/
theorem source_valid : ValidGraphEvents work batch := by
  have failed : TaskAt work failure [owner.ref] none (.object [] (.error 1)) :=
    ⟨[⟨owner, []⟩], [], { result := .error 1, cause := some 1 }, .empty, [], rfl, rfl, rfl⟩
  have succeeded : TaskAt work producer [owner.ref] none (.object [] (.ok (value.data, 0))) :=
    ⟨[⟨owner, []⟩], [], { result := .ok (value.data, 0) }, children, [], rfl, rfl, rfl⟩
  have first : ValidGraphEvents work [.taskFailure failure 1] :=
    .append .nil ⟨_, _, _, failed⟩
      (by simp [GraphEvent.Fresh, GraphEvent.identities])
      ⟨_, _, _, failed, by intro source impossible; cases impossible⟩
  exact .append first ⟨_, _, succeeded, rfl, rfl⟩
    (by simp [success, GraphEvent.Fresh, GraphEvent.identities, producer, failure])
    ⟨_, _, _, succeeded, by intro source impossible; cases impossible⟩

/-- Batch-entry eligibility admits the success even though the failure retires its task. -/
theorem buffered_source_admitted : inputsStarted work [batch] = true := by cbv

/-- The consumed success appears in source history, but its child chunk is never integrated. -/
theorem ignored_success_does_not_register_children
    : producer ∈ batch.flatMap GraphEvent.successes
      ∧ (initial.handleGraphEvents batch).1.task? nested = none
      ∧ owner.ref ∈ (initial.handleGraphEvents batch).1.cancelledGroups := by
  constructor
  · simp [batch, success, GraphEvent.successes]
  · constructor
    · cbv
    · cbv; exact List.mem_cons_self

/-- The old unconditional source-success registration predicate is too strong for this batch. -/
theorem unconditional_registration_fails
    : ¬ (initial.handleGraphEvents batch).1.SuccessfulProducerRegistrations work
          batch := by
  intro registered
  have known : TaskAt work nested [child.ref] (some producer)
      (.object [] (.ok ([("b", .scalar "b")], 0))) :=
    ⟨[⟨child, []⟩], [], { result := .ok ([("b", .scalar "b")], 0) }, .empty, [owner.ref],
      rfl, rfl, rfl⟩
  obtain ⟨task, member, identity, groups⟩ := registered _ _ _ _ known
    (.inr ⟨_, rfl, ignored_success_does_not_register_children.1⟩)
  have tasks : (initial.handleGraphEvents batch).1.tasks
      = [⟨producer, [owner]⟩, ⟨failure, [owner]⟩] := by cbv
  rw [tasks] at member
  rcases List.mem_cons.mp member with rfl | last
  · cases identity
  · have same := List.mem_singleton.mp last
    subst task
    cases identity

end GraphQL.IncrementalDelivery.Tests.BufferedSuccessfulProducer
