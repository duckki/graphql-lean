import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupMembershipOrder

/-! Source freshness excludes reverse producer edges in concrete registration order. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Registration chunks have exact source producers, not inferred publication positions
-----------------------------------------------------------------------------------------

/-- Immediate task definitions offered by an input, before the queue's acceptance guard.
This proof projection is not stored by the implementation and includes ignored chunks.
-/
def GraphEvent.childTasks : GraphEvent → List Task
  | .taskSuccess _ result => result.work.tasks
  | .streamItems _ items => items.flatMap (fun item => item.work.tasks)
  | _ => []

/-- Each handler appends either its complete immediate task chunk or nothing.
Witness: the actual acceptance guards and permanent-registry equations; cleanup never
removes or reorders permanent task registrations.
-/
theorem State.handleGraphEvent_taskChunk (queue : State) (event : GraphEvent)
    : (queue.handleGraphEvent event).1.tasks = queue.tasks
      ∨ (queue.handleGraphEvent event).1.tasks = queue.tasks ++ event.childTasks := by
  cases event with
  | taskSuccess occurrence result =>
      cases found : queue.taskNode? occurrence with
      | none => left; simp only [State.handleGraphEvent, State.taskSuccess, found]
      | some node =>
          cases healthy : queue.taskHasHealthyOwner node.task with
          | false => left; rw [State.handleGraphEvent,
              State.taskSuccess_of_noHealthyOwner found healthy]; rfl
          | true => exact .inr (State.taskSuccess_tasks found healthy)
  | taskFailure occurrence errors =>
      exact .inl (queue.taskFailure_tasks occurrence errors)
  | streamItems stream items =>
      cases active : queue.rootStreams.contains stream.key with
      | false =>
          left
          simp only [State.handleGraphEvent, State.streamItems, active, Bool.not_false,
            ↓reduceIte]
      | true => exact .inr (queue.streamItems_tasks stream items active)
  | streamSuccess stream =>
      left
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> rfl
  | streamFailure stream errors =>
      left
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> rfl

/-- Every offered child task has a producer that succeeds in that same source event.
Witness: exact task/item child-work matching supplies its structural producer.
-/
theorem GraphEvent.MatchesWork.childTasks_producer {work event}
    (matching : GraphEvent.MatchesWork work event) {task : Task}
    (member : task ∈ event.childTasks)
    : ∃ producer ∈ event.successes,
        TaskHasProducer work task.occurrence (some producer) := by
  cases event with
  | taskSuccess occurrence result =>
      obtain ⟨_, payload, _, known⟩ := matching.childTask_producer member
      exact ⟨occurrence, List.mem_cons_self, _, payload, known⟩
  | streamItems stream items =>
      obtain ⟨item, selected, child⟩ := List.mem_flatMap.mp member
      obtain ⟨_, payload, _, known⟩ := matching.streamItem_childTask_producer selected child
      exact ⟨item.occurrence, List.mem_map.mpr ⟨item, selected, rfl⟩, _, payload, known⟩
  | taskFailure | streamSuccess | streamFailure => cases member

/-- A freshly offered child has not settled in any preceding source input.
Witness: earlier child settlement would require this event's producer to settle twice.
-/
theorem GraphEvent.MatchesWork.childTasks_unsettled {work before event}
    (matching : GraphEvent.MatchesWork work event) (valid : ValidGraphEvents work before)
    (fresh : event.Fresh before) {task : Task} (member : task ∈ event.childTasks)
    : task.occurrence ∉ before.flatMap (fun prior => prior.identities.1) := by
  cases event with
  | taskSuccess occurrence result => exact matching.childTasksFresh valid fresh member
  | streamItems stream items =>
      obtain ⟨item, selected, child⟩ := List.mem_flatMap.mp member
      exact matching.streamItem_childTasksFresh valid fresh selected child
  | taskFailure | streamSuccess | streamFailure => cases member

/-- A source event never supplies its own child task as a simultaneous producer success.
Witness: object production strictly decreases structural rank; stream successes carry
item identities while their newly registered tasks carry object identities.
-/
theorem GraphEvent.MatchesWork.childTasks_not_success {work event}
    (matching : GraphEvent.MatchesWork work event) {task : Task}
    (member : task ∈ event.childTasks)
    : task.occurrence ∉ event.successes := by
  cases event with
  | taskSuccess occurrence result =>
      obtain ⟨_, _, _, known⟩ := matching.childTask_producer member
      intro success
      have same : task.occurrence = occurrence := List.mem_singleton.mp success
      have lower := known.producer_dependency.1
      rw [same] at lower
      exact Nat.lt_irrefl _ lower
  | streamItems stream items =>
      obtain ⟨item, selected, child⟩ := List.mem_flatMap.mp member
      obtain ⟨address, _, occurrence, _⟩ :=
        matching.streamItem_childTask_producer selected child
      intro success
      obtain ⟨source, sourceMember, same⟩ := List.mem_map.mp success
      obtain ⟨_, _, known, _⟩ := matching source sourceMember
      rw [same, occurrence] at known
      cases StructuralEquivalence.taskAt_of_current known
  | taskFailure | streamSuccess | streamFailure => cases member

-----------------------------------------------------------------------------------------
-- Source-ready registrations rule out a child appearing before its producer
-----------------------------------------------------------------------------------------

/-- Each registered task's producer has succeeded in the supplied source prefix.
This says nothing about publication: a successful producer can still be buffered.
-/
def TaskProducersSucceeded (work : Execution.Work) (tasks : List Task)
    (received : List GraphEvent)
    : Prop :=
  ∀ task ∈ tasks,
    ∀ producer,
      TaskHasProducer work task.occurrence (some producer)
      → producer ∈ received.flatMap GraphEvent.successes

/-- Registration order contains no reversed structural producer edge.
The relation is pairwise so filtering memberships and flush selections preserves it.
-/
def ProducerOrder (work : Execution.Work) (occurrences : List Occurrence) : Prop :=
  occurrences.Pairwise (fun earlier later => ¬TaskHasProducer work earlier (some later))

/-- Root registrations have neither a producer prerequisite nor a reversed producer edge.
Witness: root lowering assigns every immediate task the absent producer.
-/
theorem createWorkQueue_producerOrder (work : Execution.Work)
    : TaskProducersSucceeded work (State.initialize (Work.fromExecution work)).tasks []
      ∧ ProducerOrder work
          ((State.initialize (Work.fromExecution work)).tasks.map Task.occurrence) := by
  rw [createWorkQueue_tasks]
  have root (task : Task) (member : task ∈ (Work.fromExecution work).tasks) (producer : Occurrence)
      : ¬TaskHasProducer work task.occurrence (some producer) := by
    obtain ⟨_, _, _, known⟩ := workFromSpec_tasks_taskAt Located.root member
    rintro ⟨_, _, other⟩
    have impossible := (known.unique other).2.1
    cases impossible
  refine ⟨
    fun task member producer known => False.elim (root task member producer known),
    ?_
  ⟩
  apply List.pairwise_of_forall_mem_list
  intro occurrence member producer _
  obtain ⟨task, member, same⟩ := List.mem_map.mp member
  exact same ▸ root task member producer

/-- One valid source event preserves producer order while extending producer settlements.
Witness: old prerequisites stay in the old prefix. Newly offered tasks have fresh,
unsettled identities, so none can be the producer of an old registered child. Within
the new chunk, producer identities are source successes rather than sibling tasks.
-/
theorem State.handleGraphEvent_producerOrder {queue : State} {work before event}
    (ready : TaskProducersSucceeded work queue.tasks before)
    (ordered : ProducerOrder work (queue.tasks.map Task.occurrence))
    (valid : ValidGraphEvents work before) (matching : GraphEvent.MatchesWork work event)
    (fresh : event.Fresh before)
    : TaskProducersSucceeded work (queue.handleGraphEvent event).1.tasks
        (before ++ [event])
      ∧ ProducerOrder work
          ((queue.handleGraphEvent event).1.tasks.map Task.occurrence) := by
  have later (tasks : List Task) (prior : TaskProducersSucceeded work tasks before)
      : TaskProducersSucceeded work tasks (before ++ [event]) := by
    intro task member producer known
    rw [List.flatMap_append]
    exact List.mem_append_left _ (prior task member producer known)
  rcases queue.handleGraphEvent_taskChunk event with unchanged | appended
  · rw [unchanged]
    exact ⟨later _ ready, ordered⟩
  rw [appended]
  have childProducer (task : Task) (member : task ∈ event.childTasks) (producer : Occurrence)
      (known : TaskHasProducer work task.occurrence (some producer))
      : producer ∈ event.successes := by
    obtain ⟨source, selected, owners, payload, descriptor⟩ :=
      matching.childTasks_producer member
    obtain ⟨_, _, other⟩ := known
    have same := Option.some.inj (descriptor.unique other).2.1
    exact same ▸ selected
  refine ⟨?_, ?_⟩
  · intro task member producer known
    rw [List.flatMap_append, List.flatMap_singleton]
    rcases List.mem_append.mp member with old | new
    · exact List.mem_append_left _ (ready task old producer known)
    · exact List.mem_append_right _ (childProducer task new producer known)
  · unfold ProducerOrder
    rw [List.map_append, List.pairwise_append]
    refine ⟨ordered, ?_, ?_⟩
    · apply List.pairwise_of_forall_mem_list
      intro child childMember producer producerMember known
      obtain ⟨task, member, rfl⟩ := List.mem_map.mp childMember
      obtain ⟨parent, parentMember, rfl⟩ := List.mem_map.mp producerMember
      exact matching.childTasks_not_success parentMember
        (childProducer task member parent.occurrence known)
    · intro child childMember producer producerMember known
      obtain ⟨task, member, rfl⟩ := List.mem_map.mp childMember
      obtain ⟨parent, parentMember, rfl⟩ := List.mem_map.mp producerMember
      exact matching.childTasks_unsettled valid fresh parentMember
        (GraphEvent.successes_mem_settled (ready task member parent.occurrence known))

/-- Every source-valid replay has producer-ready registrations in non-reversed order.
Witness: induction over source prefixes using the actual append-or-ignore registry
equation. No generated-work, announcement, or publication-admission premise is needed.
-/
theorem createWorkQueue_replayGraphEvents_producerOrder {work events}
    (valid : ValidGraphEvents work events)
    : TaskProducersSucceeded work
        ((State.initialize (Work.fromExecution work)).replayGraphEvents events).tasks
        events
      ∧ ProducerOrder work
          (((State.initialize (Work.fromExecution work)).replayGraphEvents
              events).tasks.map
            Task.occurrence) := by
  induction valid with
  | nil => exact createWorkQueue_producerOrder work
  | @append before event valid matching fresh _ ih =>
      simpa only [State.replayGraphEvents, List.foldl_append, List.foldl_cons,
        List.foldl_nil]
        using State.handleGraphEvent_producerOrder ih.1 ih.2 valid matching fresh

-----------------------------------------------------------------------------------------
-- Subsequence transport gives strict ordering within an actual flush selection
-----------------------------------------------------------------------------------------

/-- Removing occurrences preserves the absence of reversed producer edges.
Witness: pairwise relations restrict to ordered subsequences.
-/
theorem ProducerOrder.sublist {work before after} (ordered : ProducerOrder work after)
    (selected : before.Sublist after)
    : ProducerOrder work before :=
  List.Pairwise.sublist selected ordered

/-- A present producer must occur strictly before its child in any producer-ordered list.
Witness: reverse indices contradict the pairwise relation; equal indices contradict the
strict dependency rank of a structural producer. List uniqueness is not required.
-/
theorem ProducerOrder.producer_before {work occurrences child parent}
    {childIndex parentIndex : Nat}
    (ordered : ProducerOrder work occurrences)
    (childAt : occurrences[childIndex]? = some child)
    (parentAt : occurrences[parentIndex]? = some parent)
    (known : TaskHasProducer work child (some parent))
    : parentIndex < childIndex := by
  obtain ⟨childBound, childEq⟩ := List.getElem?_eq_some_iff.mp childAt
  obtain ⟨parentBound, parentEq⟩ := List.getElem?_eq_some_iff.mp parentAt
  by_cases reverse : childIndex < parentIndex
  · have excluded := List.pairwise_iff_getElem.mp ordered
      childIndex parentIndex childBound parentBound reverse
    rw [childEq, parentEq] at excluded
    exact False.elim (excluded known)
  by_cases sameIndex : childIndex = parentIndex
  · have same : child = parent := by
      rw [sameIndex] at childAt
      exact Option.some.inj (childAt.symm.trans parentAt)
    obtain ⟨_, _, descriptor⟩ := known
    have lower := descriptor.producer_dependency.1
    rw [same] at lower
    exact False.elim (Nat.lt_irrefl _ lower)
  omega

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
