import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SourceRegistrationCompleteness
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CancellationMonotonicity

/-! Successful source callbacks expose children unless every object-producer owner retired
through cancellation. This is proof evidence, not an additional runtime registration rule.
-/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Every owner of the named object producer is marked cancelled in the concrete queue. -/
def State.ObjectProducerCancelled (queue : State) (work : Execution.Work)
    (producer : Option Occurrence)
    : Prop :=
  ∃ address owners,
    producer = some (.executionGroup address)
    ∧ TaskHasOwners work (.executionGroup address) owners
    ∧ ∀ ref ∈ owners, ref ∈ queue.cancelledGroups

/-- Root tasks and children of successful source producers are registered, or their object
producer has no uncancelled owner. Ignored success callbacks need not integrate children.
Item callbacks use source-ordered stream liveness and always integrate their children.
-/
def State.ProducerRegistrationAccounting (queue : State) (work : Execution.Work)
    (before : List GraphEvent)
    : Prop :=
  ∀ address owners producer payload,
    TaskAt work (.executionGroup address) owners producer payload
    → (producer = none
        ∨ ∃ source, producer = some source ∧ source ∈ before.flatMap GraphEvent.successes)
    → (∃ task ∈ queue.tasks,
        task.occurrence = .executionGroup address
        ∧ task.groups.map Execution.DeliveryNode.ref = owners)
      ∨ queue.ObjectProducerCancelled work producer

/-- Initial lowering has registered every root task; no cancellation alternative is needed. -/
theorem createWorkQueue_producerRegistrationAccounting (work : Execution.Work)
    : (State.initialize (Work.fromExecution work)).ProducerRegistrationAccounting work
        [] := by
  intro address owners producer payload known available
  exact .inl (createWorkQueue_successfulProducerRegistrations work _ _ _ _ known available)

/-- Root registration cannot use the object-producer cancellation alternative. -/
theorem State.ProducerRegistrationAccounting.root_registered
    {queue work before address owners payload}
    (prior : State.ProducerRegistrationAccounting queue work before)
    (known : TaskAt work (.executionGroup address) owners none payload)
    : ∃ task ∈ queue.tasks,
        task.occurrence = .executionGroup address
        ∧ task.groups.map Execution.DeliveryNode.ref = owners := by
  rcases prior _ _ _ _ known (.inl rfl) with registered | ⟨source, groups, impossible, rest⟩
  · exact registered
  · cases impossible

/-- A consumed item success always registers its structural object children. -/
theorem State.ProducerRegistrationAccounting.item_registered
    {queue work before address owners payload source index}
    (prior : State.ProducerRegistrationAccounting queue work before)
    (known
      : TaskAt work (.executionGroup address) owners (some (.item source index)) payload)
    (success : .item source index ∈ before.flatMap GraphEvent.successes)
    : ∃ task ∈ queue.tasks,
        task.occurrence = .executionGroup address
        ∧ task.groups.map Execution.DeliveryNode.ref = owners := by
  rcases prior _ _ _ _ known (.inr ⟨_, rfl, success⟩) with registered | cancelled
  · exact registered
  · obtain ⟨producer, groups, impossible, rest⟩ := cancelled
    cases impossible

/-- An object producer with an uncancelled contributor registers every child. -/
theorem State.ProducerRegistrationAccounting.object_registered
    {queue work before address owners payload source producerOwners ref}
    (prior : State.ProducerRegistrationAccounting queue work before)
    (known
      : TaskAt work (.executionGroup address) owners (some (.executionGroup source))
          payload)
    (success : .executionGroup source ∈ before.flatMap GraphEvent.successes)
    (producer : TaskHasOwners work (.executionGroup source) producerOwners)
    (contributes : ref ∈ producerOwners) (uncancelled : ref ∉ queue.cancelledGroups)
    : ∃ task ∈ queue.tasks,
        task.occurrence = .executionGroup address
        ∧ task.groups.map Execution.DeliveryNode.ref = owners := by
  rcases prior _ _ _ _ known (.inr ⟨_, rfl, success⟩) with registered | cancelled
  · exact registered
  · obtain ⟨other, groups, same, descriptor, all⟩ := cancelled
    have equal : source = other := by simpa only [Option.some.injEq,
      Occurrence.executionGroup.injEq] using same
    subst other
    obtain ⟨birth, value, actual⟩ := producer
    obtain ⟨otherBirth, otherValue, otherKnown⟩ := descriptor
    have sameOwners := (actual.unique otherKnown).1
    exact (uncancelled (all ref (sameOwners ▸ contributes))).elim

/-- Permanent cancellation marks survive every handler. -/
theorem State.ObjectProducerCancelled.handleGraphEvent {queue work producer}
    (prior : State.ObjectProducerCancelled queue work producer) (event : GraphEvent)
    (available : List (Occurrence × Nat))
    : (queue.handleGraphEvent event available).1.ObjectProducerCancelled work
        producer := by
  obtain ⟨address, owners, same, known, cancelled⟩ := prior
  exact ⟨address, owners, same, known,
    fun ref member => queue.handleGraphEvent_cancelledGroups_subset event available
      (cancelled ref member)⟩

/-- One matching callback retains complete child registration or an actual producer
cancellation certificate. Missing object callbacks use their preexisting retirement;
stream items require the existing live-stream guard.
-/
theorem State.ProducerRegistrationAccounting.handleGraphEvent {queue work before}
    (prior : State.ProducerRegistrationAccounting queue work before)
    (event : GraphEvent) (matching : event.MatchesWork work)
    (available : List (Occurrence × Nat))
    (missing
      : ∀ occurrence result,
          event = .taskSuccess occurrence result
          → queue.taskNode? occurrence = none
          → queue.ObjectProducerCancelled work (some occurrence))
    (itemsLive
      : ∀ stream items,
          event = .streamItems stream items
          → queue.acceptsGraphEvent (.streamItems stream items) = true)
    : (queue.handleGraphEvent event available).1.ProducerRegistrationAccounting work
        (before ++ [event]) := by
  intro address owners producer payload known supported
  have old (support : producer = none ∨ ∃ source, producer = some source ∧
      source ∈ before.flatMap GraphEvent.successes) :
      (∃ task ∈ (queue.handleGraphEvent event available).1.tasks,
        task.occurrence = .executionGroup address ∧
          task.groups.map Execution.DeliveryNode.ref = owners)
      ∨ (queue.handleGraphEvent event available).1.ObjectProducerCancelled work producer := by
    rcases prior _ _ _ _ known support with registered | cancelled
    · obtain ⟨task, member, occurrence, groups⟩ := registered
      exact .inl ⟨task, queue.handleGraphEvent_tasks_subset event available member,
        occurrence, groups⟩
    · exact .inr (cancelled.handleGraphEvent event available)
  rcases supported with root | ⟨source, same, success⟩
  · exact old (.inl root)
  · rw [List.flatMap_append, List.flatMap_singleton] at success
    rcases List.mem_append.mp success with earlier | current
    · exact old (.inr ⟨source, same, earlier⟩)
    · subst producer
      cases event with
      | taskSuccess occurrence result =>
          have equal : source = occurrence := List.mem_singleton.mp current
          subst source
          cases found : queue.taskNode? occurrence with
          | none =>
              exact .inr ((missing occurrence result rfl found).handleGraphEvent _ available)
          | some node =>
              have eligible : (queue.cacheTaskFailures available).acceptsGraphEvent
                  (.taskSuccess occurrence result) = true := by
                rw [State.cacheTaskFailures_acceptsGraphEvent]
                simp only [State.acceptsGraphEvent, found, Option.isSome_some]
              cases cached : (queue.cacheTaskFailures available).taskNode? occurrence with
              | none => simp only [State.acceptsGraphEvent, cached, Option.isSome_none,
                  Bool.false_eq_true] at eligible
              | some active =>
                  exact .inl (State.taskSuccess_child_registered cached matching known available)
      | streamItems stream items =>
          obtain ⟨item, member, equal⟩ := List.mem_map.mp current
          have descriptor : TaskAt work (.executionGroup address) owners
              (some item.occurrence) payload := equal.symm ▸ known
          have cached : (queue.cacheTaskFailures available).acceptsGraphEvent
              (.streamItems stream items) = true := by
            rw [State.cacheTaskFailures_acceptsGraphEvent]
            exact itemsLive _ _ rfl
          exact .inl
            (State.streamItems_child_registered cached matching member descriptor
              available)
      | taskFailure | streamSuccess | streamFailure | groupFailure => cases current

/-- The control-only terminal flag preserves registration and cancellation evidence. -/
theorem State.ProducerRegistrationAccounting.withTerminated {queue work before}
    (prior : State.ProducerRegistrationAccounting queue work before) (terminated : Bool)
    : ({ queue with terminated } : State).ProducerRegistrationAccounting work before :=
  prior

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
