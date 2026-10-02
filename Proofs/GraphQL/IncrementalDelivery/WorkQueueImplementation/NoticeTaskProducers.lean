import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupNoticeTaskProvenance
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskProducerOrder

/-! Retained notice tasks were registered only after their source producers succeeded. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Registration prerequisites survive every internal carrier boundary
-----------------------------------------------------------------------------------------

/-- Extending the received source preserves successful prerequisites of registered tasks.
Witness: every old successful source occurrence remains in the extended event list.
-/
theorem TaskProducersSucceeded.mono {work tasks before after}
    (ready : TaskProducersSucceeded work tasks before) (included : before.Subset after)
    : TaskProducersSucceeded work tasks after := by
  intro task member producer known
  obtain ⟨event, received, success⟩ := List.mem_flatMap.mp (ready task member producer known)
  exact List.mem_flatMap.mpr ⟨event, included received, success⟩

/-- Integration adds only tasks whose structural producer is a supplied source success.
Witness: the permanent registry is exactly the old registry followed by incoming tasks.
-/
theorem TaskProducersSucceeded.maybeIntegrateWork {queue : State} {work received}
    (ready : TaskProducersSucceeded work queue.tasks received)
    (children : Work) (parent : Option Occurrence)
    (incoming : TaskProducersSucceeded work children.tasks received)
    : TaskProducersSucceeded work (queue.maybeIntegrateWork children parent).1.tasks
        received := by
  rw [State.maybeIntegrateWork_tasks_append]
  intro task member
  exact (List.mem_append.mp member).elim (ready task) (incoming task)

/-- An owner-fold prefix cannot change any registered task's producer prerequisite.
Witness: its permanent task registry is unchanged, even when live memberships disappear.
-/
theorem TaskProducersSucceeded.successGroupFold {queue : State} {work received}
    (ready : TaskProducersSucceeded work queue.tasks received)
    (groups : List Execution.DeliveryNode)
    : TaskProducersSucceeded work
        (groups.foldl successGroupStep (queue, [], {})).1.tasks received := by
  rw [successGroupFold_tasks]
  exact ready

/-- Starting released work keeps its already registered producer prerequisites.
Witness: activation leaves permanent task definitions unchanged.
-/
theorem TaskProducersSucceeded.startNewWork {queue : State} {work received}
    (ready : TaskProducersSucceeded work queue.tasks received) (released : NewWork)
    : TaskProducersSucceeded work (queue.startNewWork released).tasks received := by
  rw [(State.startNewWork_groupCore _ _).2.1]
  exact ready

/-- Every bounded drain prefix preserves successful source prerequisites.
Witness: successful closure, activation, and failed cleanup leave the permanent registry
unchanged. This applies before later drain steps remove additional live records.
-/
theorem TaskProducersSucceeded.drainReadyGroups_go {queue : State} {work received}
    (ready : TaskProducersSucceeded work queue.tasks received) (fuel : Nat)
    : TaskProducersSucceeded work (State.drainReadyGroups.go fuel queue).1.tasks
        received := by
  apply State.drainReadyGroups_go_preserves
    (fun current => TaskProducersSucceeded work current.tasks received) (valid := ready)
  · intro current node prior _ _ _ _
    apply TaskProducersSucceeded.startNewWork
    rwa [State.finishGroupSuccess_tasks]
  · intro current node errors prior _ _ _
    exact prior

/-- An item integration adds only tasks produced by that item from the actual source input.
Witness: source matching supplies each incoming task's unique item producer; old task
prerequisites remain unchanged. Items need not have published at the integration step.
-/
theorem TaskProducersSucceeded.integrateStreamItem {queue : State}
    {work received stream items}
    (ready : TaskProducersSucceeded work queue.tasks received)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (input : GraphEvent.streamItems stream items ∈ received) {item : StreamItem}
    (member : item ∈ items)
    : TaskProducersSucceeded work (queue.integrateStreamItem item).tasks received := by
  rw [State.integrateStreamItem_tasks]
  intro task registered producer known
  rcases List.mem_append.mp registered with old | child
  · exact ready task old producer known
  · obtain ⟨source, success, owners, payload, descriptor⟩ :=
      matching.childTasks_producer (List.mem_flatMap.mpr ⟨item, member, child⟩)
    obtain ⟨_, _, other⟩ := known
    have same := Option.some.inj (descriptor.unique other).2.1
    exact List.mem_flatMap.mpr ⟨_, input, same ▸ success⟩

/-- Every item-preparation prefix keeps successful source prerequisites for its tasks.
Witness: fold the preceding registration rule over any supplied subset of this input's
items. The same received source is retained throughout, including the current input.
-/
theorem TaskProducersSucceeded.preparedStreamItems {queue : State}
    {work received stream items}
    (ready : TaskProducersSucceeded work queue.tasks received)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (input : GraphEvent.streamItems stream items ∈ received) (earlier : List StreamItem)
    (included : earlier.Subset items)
    : TaskProducersSucceeded work (queue.preparedStreamItems earlier).tasks received := by
  induction earlier generalizing queue with
  | nil => exact ready
  | cons item rest ih =>
      rw [State.preparedStreamItems_cons]
      exact ih (ready.integrateStreamItem matching input (included List.mem_cons_self))
        (fun _ member => included (List.mem_cons_of_mem _ member))

-----------------------------------------------------------------------------------------
-- Matching source replay supplies the prerequisites without notice-admission assumptions
-----------------------------------------------------------------------------------------

/-- A successful task handler's preparation has source-ready task registrations.
Witness: valid prior replay supplies old prerequisites; exact source matching identifies
the incoming children's producer as this task's successful settlement. No output or
announcement admission is assumed, and the producer may still be buffered.
-/
theorem createWorkQueue_taskSuccess_prepared_producersSucceeded
    {work before occurrence result after}
    (valid : ValidGraphEvents work (before ++ .taskSuccess occurrence result :: after))
    (incoming : TaskNode)
    : let current := (State.initialize (Work.fromExecution work)).replayGraphEvents before
      let stored := current.putTaskNode { incoming with value := some result.value }
      let prepared := (stored.maybeIntegrateWork result.work (some occurrence)).1
      TaskProducersSucceeded work prepared.tasks
        (before ++ .taskSuccess occurrence result :: after) := by
  have prior := valid.prefix (List.prefix_append before (.taskSuccess occurrence result :: after))
  have ready := (createWorkQueue_replayGraphEvents_producerOrder prior).1.mono
    (List.subset_append_left before (.taskSuccess occurrence result :: after))
  have matching := valid.eachMatches (List.mem_append_right before List.mem_cons_self)
  intro current stored prepared
  have storedReady : TaskProducersSucceeded work stored.tasks
      (before ++ .taskSuccess occurrence result :: after) := ready
  apply TaskProducersSucceeded.maybeIntegrateWork storedReady
  intro task member producer known
  obtain ⟨source, success, owners, payload, descriptor⟩ := matching.childTasks_producer member
  obtain ⟨_, _, other⟩ := known
  have same := Option.some.inj (descriptor.unique other).2.1
  exact List.mem_flatMap.mpr
    ⟨_, List.mem_append_right before List.mem_cons_self, same ▸ success⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
