import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.MembershipExclusionHandlers
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamPreparation

/-! Source-ready registration makes delivered membership exclusions permanent. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Exclusion preservation itself needs no publication inventory or output matching
-----------------------------------------------------------------------------------------

/-- A single-pass owner fold cannot reintroduce an absent task membership.
Witness: counter-only updates retain the membership lists, and successful flushes remove
tasks globally. Accumulated values and releases do not change this invariant.
-/
theorem State.TaskMembershipAbsent.successGroupFold {queue : State} {occurrence}
    (absent : queue.TaskMembershipAbsent occurrence)
    (groups : List Execution.DeliveryNode) (events : List WorkQueueEvent)
    (released : NewWork)
    : (groups.foldl successGroupStep (queue, events, released)).1.TaskMembershipAbsent
        occurrence := by
  induction groups generalizing queue events released with
  | nil => exact absent
  | cons group rest ih =>
      simp only [List.foldl_cons, successGroupStep]
      split
      · exact ih absent _ _
      · rename_i node found
        have updated := absent.putGroupNode { node with pending := node.pending - 1 }
          (absent node (List.mem_of_find?_eq_some found))
        split
        · exact ih (updated.finishGroupSuccess _) _ _
        · exact ih updated _ _

/-- Task success preserves an earlier exclusion when its child chunk cannot reuse it.
Witness: storage changes no membership; fresh integration, the single-pass owner fold,
activation, and every drain prefix preserve the same pointwise exclusion.
-/
theorem State.TaskMembershipAbsent.taskSuccess {queue : State} {occurrence}
    (absent : queue.TaskMembershipAbsent occurrence) (settled : Occurrence)
    (result : TaskResult)
    (fresh : ∀ child ∈ result.work.tasks, occurrence ≠ child.occurrence)
    : (queue.taskSuccess settled result).1.TaskMembershipAbsent occurrence := by
  cases found : queue.taskNode? settled with
  | none => simpa only [State.taskSuccess, found] using absent
  | some node =>
      rw [queue.taskSuccess_eq settled result node found]
      split
      · exact absent.removeTask settled
      · have stored := absent.putTaskNode { node with value := some result.value }
        have integrated := stored.maybeIntegrateWork result.work fresh (some settled)
        apply State.TaskMembershipAbsent.drainReadyGroups_go
        exact (integrated.successGroupFold node.task.groups [] {}).startNewWork _

/-- Item preparation preserves an exclusion when all offered child identities differ.
Witness: each actual integration, empty-shell pruning, and activation preserves it.
-/
theorem State.TaskMembershipAbsent.preparedStreamItems {queue : State} {occurrence}
    (absent : queue.TaskMembershipAbsent occurrence) (items : List StreamItem)
    (fresh : ∀ item ∈ items, ∀ child ∈ item.work.tasks, occurrence ≠ child.occurrence)
    : (queue.preparedStreamItems items).TaskMembershipAbsent occurrence := by
  apply State.preparedStreamItems_preserves (fun current => current.TaskMembershipAbsent occurrence)
    absent items
  intro current item member prior
  exact ((prior.maybeIntegrateWork item.work (fresh item member)).pruneEmptyGroups _).startNewWork _

/-- Stream-item handling preserves the exclusion through preparation and draining.
Witness: the leading stream event is only output; it does not modify group memberships.
-/
theorem State.TaskMembershipAbsent.streamItems {queue : State} {occurrence}
    (absent : queue.TaskMembershipAbsent occurrence) (stream : Execution.DeliveryNode)
    (items : List StreamItem)
    (fresh : ∀ item ∈ items, ∀ child ∈ item.work.tasks, occurrence ≠ child.occurrence)
    : (queue.streamItems stream items).1.TaskMembershipAbsent occurrence := by
  rw [queue.streamItems_eq stream items]
  split
  · exact absent
  · exact (absent.preparedStreamItems items fresh).drainReadyGroups_go _

/-- No handler restores an excluded occurrence unless it is offered as fresh child work.
Witness: success/item preservation handles integration; failure and stream closures only
remove records or update counters, errors, and active-stream refs.
-/
theorem State.TaskMembershipAbsent.handleGraphEvent {queue : State} {occurrence}
    (absent : queue.TaskMembershipAbsent occurrence) (event : GraphEvent)
    (fresh : ∀ child ∈ event.childTasks, occurrence ≠ child.occurrence)
    : (queue.handleGraphEvent event).1.TaskMembershipAbsent occurrence := by
  cases event with
  | taskSuccess settled result => exact absent.taskSuccess settled result fresh
  | taskFailure settled errors => exact absent.taskFailure settled errors
  | streamItems stream items =>
      exact absent.streamItems stream items (fun item member child childMember =>
        fresh child (List.mem_flatMap.mpr ⟨item, member, childMember⟩))
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> exact absent
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> exact absent

-----------------------------------------------------------------------------------------
-- The existing source laws forbid reuse of any permanently registered task identity
-----------------------------------------------------------------------------------------

/-- A fresh input's child is not already in the permanent task registry.
Witness: the child has a producer settling in this input. Prior registration would require
that same producer to have succeeded earlier, contradicting source freshness. The argument
does not require the child itself to have settled or published.
-/
theorem GraphEvent.MatchesWork.childTask_not_registered {queue : State}
    {work before event} (matching : GraphEvent.MatchesWork work event)
    (ready : TaskProducersSucceeded work queue.tasks before) (fresh : event.Fresh before)
    {child : Task} (member : child ∈ event.childTasks)
    : child.occurrence ∉ queue.tasks.map Task.occurrence := by
  intro registered
  obtain ⟨task, taskMember, same⟩ := List.mem_map.mp registered
  obtain ⟨producer, success, known⟩ := matching.childTasks_producer member
  have earlier := ready task taskMember producer (same.symm ▸ known)
  have incoming : producer ∈ event.identities.1 := by
    simpa only [List.flatMap_singleton]
      using GraphEvent.successes_mem_settled (events := [event])
        (by simpa only [List.flatMap_singleton] using success)
  exact fresh.2.2.1 producer incoming
    (GraphEvent.successes_mem_settled earlier)

/-- Registered membership exclusion survives every valid source continuation.
Witness: permanent registration persists, each incoming child differs by producer
freshness, and all handlers preserve the exclusion. No publication ledger, output
admission, generated-work premise, or host-start condition is needed.
-/
theorem State.TaskMembershipAbsent.replayGraphEvents_registered
    {queue : State} {work before occurrence}
    (absent : queue.TaskMembershipAbsent occurrence)
    (registered : occurrence ∈ queue.tasks.map Task.occurrence)
    (ready : TaskProducersSucceeded work queue.tasks before)
    (ordered : ProducerOrder work (queue.tasks.map Task.occurrence))
    (events : List GraphEvent) (valid : ValidGraphEvents work (before ++ events))
    : (queue.replayGraphEvents events).TaskMembershipAbsent occurrence := by
  induction events generalizing queue before with
  | nil => exact absent
  | cons event rest ih =>
      have earlier : (before ++ [event]).IsPrefix (before ++ event :: rest) := ⟨rest, by simp⟩
      obtain ⟨matching, fresh, _⟩ := valid.atPrefix earlier
      have continued := absent.handleGraphEvent event (by
        intro child member same
        exact matching.childTask_not_registered ready fresh member (same ▸ registered))
      have next := State.handleGraphEvent_producerOrder ready ordered
        (valid.prefix (List.prefix_append before (event :: rest))) matching fresh
      apply ih continued _ next.1 next.2
        (by simpa only [List.append_assoc, List.singleton_append] using valid)
      obtain ⟨task, member, same⟩ := List.mem_map.mp registered
      exact List.mem_map.mpr
        ⟨task, queue.handleGraphEvent_tasks_subset event member, same⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
