import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CacheEligibility
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskRegistrationReplay

/-! Consumed successful producers register their complete structural object-task chunks. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Every root task and immediate child of a consumed successful producer is registered.
The history records consumed source inputs, not cached rejection availability. -/
def State.SuccessfulProducerRegistrations (queue : State) (work : Execution.Work)
    (before : List GraphEvent)
    : Prop :=
  ∀ address owners producer payload,
    TaskAt work (.executionGroup address) owners producer payload
    → (producer = none
        ∨ ∃ source, producer = some source ∧ source ∈ before.flatMap GraphEvent.successes)
    → ∃ task ∈ queue.tasks,
        task.occurrence = .executionGroup address
        ∧ task.groups.map Execution.DeliveryNode.ref = owners

/-- Initial lowering registers every producer-free object task. -/
theorem createWorkQueue_successfulProducerRegistrations (work : Execution.Work)
    : (State.initialize (Work.fromExecution work)).SuccessfulProducerRegistrations work
        [] := by
  intro address owners producer payload known available
  rcases available with rfl | ⟨source, same, impossible⟩
  · exact TaskAt.executionGroup_initial_registered known
  · cases impossible

/-- Each accepted matching handler registers every child of its successful source inputs.
Existing registrations persist, including through cached startup removal. -/
theorem State.SuccessfulProducerRegistrations.handleGraphEvent {queue : State}
    {work before} (prior : queue.SuccessfulProducerRegistrations work before)
    (event : GraphEvent) (matching : event.MatchesWork work)
    (accepted : queue.acceptsGraphEvent event = true)
    (available : List (Occurrence × Nat))
    : (queue.handleGraphEvent event available).1.SuccessfulProducerRegistrations work
        (before ++ [event]) := by
  intro address owners producer payload known supported
  have old (support : producer = none ∨ ∃ source, producer = some source ∧
      source ∈ before.flatMap GraphEvent.successes) :
      ∃ task ∈ (queue.handleGraphEvent event available).1.tasks,
        task.occurrence = .executionGroup address ∧
          task.groups.map Execution.DeliveryNode.ref = owners := by
    obtain ⟨task, member, occurrence, groups⟩ := prior _ _ _ _ known support
    exact ⟨task, queue.handleGraphEvent_tasks_subset event available member,
      occurrence, groups⟩
  rcases supported with root | ⟨source, same, success⟩
  · exact old (.inl root)
  · rw [List.flatMap_append, List.flatMap_singleton] at success
    rcases List.mem_append.mp success with earlier | current
    · exact old (.inr ⟨source, same, earlier⟩)
    · subst producer
      have cachedAccepted : (queue.cacheTaskFailures available).acceptsGraphEvent event = true := by
        rwa [State.cacheTaskFailures_acceptsGraphEvent]
      cases event with
      | taskSuccess occurrence result =>
          have equal : source = occurrence := List.mem_singleton.mp current
          subst source
          obtain ⟨node, found⟩ : ∃ node,
              (queue.cacheTaskFailures available).taskNode? occurrence = some node := by
            cases found : (queue.cacheTaskFailures available).taskNode? occurrence with
            | none => simp only [State.acceptsGraphEvent, found, Option.isSome_none,
                Bool.false_eq_true] at cachedAccepted
            | some node => exact ⟨node, rfl⟩
          exact State.taskSuccess_child_registered found matching known available
      | streamItems stream items =>
          obtain ⟨item, member, equal⟩ := List.mem_map.mp current
          have descriptor : TaskAt work (.executionGroup address) owners
              (some item.occurrence) payload := equal.symm ▸ known
          exact State.streamItems_child_registered cachedAccepted matching member descriptor
            available
      | taskFailure | groupFailure | streamSuccess | streamFailure => cases current

/-- Changing the terminal flag does not change permanent producer registrations. -/
theorem State.SuccessfulProducerRegistrations.withTerminated {queue : State} {work before}
    (prior : queue.SuccessfulProducerRegistrations work before) (terminated : Bool)
    : ({ queue with terminated } : State).SuccessfulProducerRegistrations work before :=
  prior

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
