import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskRegistrationReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupPublication

/-! Concrete task registration places every object producer strictly before its children. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Registration order is a derived property of the existing append-only task list
-----------------------------------------------------------------------------------------

/-- At each task position, any object producer occurs in the strict earlier registry prefix.
Item producers are not task-registry entries and have their separate stream-order proof.
-/
def ObjectProducersRegisteredBefore (work : Execution.Work) (tasks : List Task) : Prop :=
  ∀ index task,
    tasks[index]? = some task
    → ∀ source,
        TaskHasProducer work task.occurrence (some (.executionGroup source))
        → ∃ parent ∈ tasks.take index, parent.occurrence = .executionGroup source

/-- Appending tasks preserves order if each new object producer is already registered.
Witness: split the selected index between old and new registries; old strict prefixes
are unchanged, while every new prefix contains the complete old registry.
-/
theorem ObjectProducersRegisteredBefore.append {work before added}
    (ordered : ObjectProducersRegisteredBefore work before)
    (supported
      : ∀ task ∈ added,
          ∀ source,
            TaskHasProducer work task.occurrence (some (.executionGroup source))
            → ∃ parent ∈ before, parent.occurrence = .executionGroup source)
    : ObjectProducersRegisteredBefore work (before ++ added) := by
  intro index task selected source known
  by_cases early : index < before.length
  · obtain ⟨parent, member, same⟩ :=
      ordered index task ((List.getElem?_append_left early).symm.trans selected) source known
    exact ⟨parent, by simpa only [List.take_append_of_le_length (Nat.le_of_lt early)]
      using member, same⟩
  · have late : before.length ≤ index := Nat.le_of_not_gt early
    have found := (List.getElem?_append_right late).symm.trans selected
    obtain ⟨parent, member, same⟩ := supported task (List.mem_of_getElem? found) source known
    exact ⟨parent, by
      rw [List.take_append, List.take_of_length_le late]
      exact List.mem_append_left _ member, same⟩

/-- Initial task lowering contains only producer-free tasks, so registration is ordered.
Witness: each immediate task inherits the root location's absent producer.
-/
theorem createWorkQueue_objectProducersRegisteredBefore (work : Execution.Work)
    : ObjectProducersRegisteredBefore work
        (State.initialize (Work.fromExecution work)).tasks := by
  rw [createWorkQueue_tasks]
  intro index task selected source known
  obtain ⟨_, _, _, located⟩ := workFromSpec_tasks_taskAt Located.root
    (List.mem_of_getElem? selected)
  obtain ⟨owners, payload, other⟩ := known
  have impossible := (located.unique other).2.1
  cases impossible

-----------------------------------------------------------------------------------------
-- A successful host task is registered before its child-work integration
-----------------------------------------------------------------------------------------

/-- A matching success appends children only after its already registered object producer.
Witness: the real task-node lookup identifies the parent's permanent registration; exact
child lowering fixes every new task's structural producer. Ignored success appends nothing.
-/
theorem State.taskSuccess_objectProducersRegisteredBefore {queue : State}
    {work occurrence result} (ordered : ObjectProducersRegisteredBefore work queue.tasks)
    (started : queue.StartedTasksRegistered)
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    : ObjectProducersRegisteredBefore work
        (queue.taskSuccess occurrence result).1.tasks := by
  cases found : queue.taskNode? occurrence with
  | none => simpa only [State.taskSuccess, found] using ordered
  | some node =>
      cases healthy : queue.taskHasHealthyOwner node.task with
      | false =>
          rw [State.taskSuccess_of_noHealthyOwner found healthy]
          exact ordered
      | true =>
          rw [State.taskSuccess_tasks found healthy]
          apply ordered.append
          intro task member source known
          obtain ⟨_, _, _, located⟩ := matching.childTask_producer member
          obtain ⟨_, _, other⟩ := known
          have same := Option.some.inj (located.unique other).2.1
          have lookup := State.taskNode?_some found
          exact ⟨node.task, started node lookup.1, lookup.2.trans same⟩

/-- Stream-item integration appends only item-produced tasks, never object-produced tasks.
Witness: exact item child lowering identifies the producer constructor, so the new
object-producer obligation is impossible. Existing registry order is preserved.
-/
theorem State.streamItems_objectProducersRegisteredBefore {queue : State}
    {work stream items} (ordered : ObjectProducersRegisteredBefore work queue.tasks)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    : ObjectProducersRegisteredBefore work (queue.streamItems stream items).1.tasks := by
  cases active : queue.rootStreams.contains stream.key with
  | false =>
      simpa only [State.streamItems, active, Bool.not_false, ↓reduceIte] using ordered
  | true =>
      rw [queue.streamItems_tasks stream items active]
      apply ordered.append
      intro task member source known
      obtain ⟨item, itemMember, taskMember⟩ := List.mem_flatMap.mp member
      obtain ⟨_, _, _, located⟩ := matching.streamItem_childTask_producer itemMember taskMember
      obtain ⟨_, _, other⟩ := known
      have same := Option.some.inj (located.unique other).2.1
      obtain ⟨_, _, descriptor, _⟩ := matching item itemMember
      rw [same] at descriptor
      simp [TaskAt] at descriptor

/-- Every matching handler preserves object-producer registration order.
Witness: successful inputs append supported chunks; failure and stream controls preserve
the permanent task registry. The started-task invariant is concrete bookkeeping only.
-/
theorem State.handleGraphEvent_objectProducersRegisteredBefore {queue : State} {work}
    (ordered : ObjectProducersRegisteredBefore work queue.tasks)
    (started : queue.StartedTasksRegistered) (event : GraphEvent)
    (matching : event.MatchesWork work)
    : ObjectProducersRegisteredBefore work (queue.handleGraphEvent event).1.tasks := by
  cases event with
  | taskSuccess =>
      exact State.taskSuccess_objectProducersRegisteredBefore ordered started matching
  | streamItems =>
      exact State.streamItems_objectProducersRegisteredBefore ordered matching
  | taskFailure occurrence errors =>
      simpa only [State.handleGraphEvent, State.taskFailure_tasks] using ordered
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> exact ordered
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> exact ordered

/-- Actual valid replay registers every object producer before each of its children.
Witness: initial immediate lowering and handler induction, with started-task registration
preserved by the executable transitions. No generated-work or start-admission premise is
needed; this is registration order, not yet observable publication order.
-/
theorem createWorkQueue_replayGraphEvents_objectProducersRegisteredBefore {work events}
    (valid : ValidGraphEvents work events)
    : ObjectProducersRegisteredBefore work
        ((State.initialize (Work.fromExecution work)).replayGraphEvents
          events).tasks := by
  have loop (more : List GraphEvent) (queue : State)
      (ordered : ObjectProducersRegisteredBefore work queue.tasks)
      (started : queue.StartedTasksRegistered)
      (matching : ∀ event ∈ more, event.MatchesWork work)
      : ObjectProducersRegisteredBefore work (queue.replayGraphEvents more).tasks := by
    induction more generalizing queue with
    | nil => exact ordered
    | cons event rest ih =>
        exact ih _ (State.handleGraphEvent_objectProducersRegisteredBefore ordered started
          event (matching event List.mem_cons_self)) (started.handleGraphEvent event)
          (fun next member => matching next (List.mem_cons_of_mem _ member))
  exact loop events _ (createWorkQueue_objectProducersRegisteredBefore work)
    (createWorkQueue_startedTasksRegistered _) (fun _ member => valid.eachMatches member)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
