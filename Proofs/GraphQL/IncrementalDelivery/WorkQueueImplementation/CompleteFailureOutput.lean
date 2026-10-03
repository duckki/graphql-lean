import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ActiveFailureCaches
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskEligibility

/-! Complete object-failure totals for every raw handler's failed group output. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Immediate failed closures retain facts about active groups at handler entry
-----------------------------------------------------------------------------------------

/-- A task-failure closure inherits any ref property of the handler's active live groups.
Witness: the owner fold only filters nodes/roots or changes counters/caches on existing
refs. Every emitted failure is selected from the current active live map.
-/
theorem State.taskFailure_groupFailure_activeProperty {queue : State}
    (property : Nat → Prop)
    (known
      : ∀ node ∈ queue.groupNodes,
          node.group.node.ref ∈ queue.rootGroups → property node.group.node.ref)
    (occurrence : Occurrence) (errors : Nat) {group count}
    (emitted
      : Execution.WorkQueueEvent.groupFailure group count
        ∈ (queue.taskFailure occurrence errors).2)
    : property group.ref := by
  let invariant := fun current : State =>
    ∀ node ∈ current.groupNodes,
      node.group.node.ref ∈ current.rootGroups → property node.group.node.ref
  have loop (groups : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent)
      (valid : invariant acc.1)
      (output : ∀ group count, Execution.WorkQueueEvent.groupFailure group count ∈ acc.2
        → property group.ref)
      : ∀ group count,
          Execution.WorkQueueEvent.groupFailure group count
            ∈ (groups.foldl (failureGroupStep errors) acc).2
          → property group.ref := by
    induction groups generalizing acc with
    | nil => exact output
    | cons owner rest ih =>
        apply ih
        · obtain ⟨current, events⟩ := acc
          dsimp only [failureGroupStep]
          split
          · exact valid
          · rename_i node found
            split
            · intro other member active
              exact valid other (List.mem_filter.mp member).1 (List.mem_filter.mp active).1
            · intro other member active
              obtain ⟨old, oldMember, same⟩ := List.mem_map.mp member
              split at same
              · subst other
                exact valid node (List.mem_of_find?_eq_some found) active
              · subst other
                exact valid old oldMember active
        · obtain ⟨current, events⟩ := acc
          dsimp only [failureGroupStep]
          split
          · exact output
          · rename_i node found
            split
            · rename_i active
              intro group count member
              rcases List.mem_append.mp member with old | new
              · exact output group count old
              · have same := Execution.WorkQueueEvent.groupFailure.inj (List.mem_singleton.mp new)
                rw [same.1]
                exact valid node (List.mem_of_find?_eq_some found)
                  (by simpa [current.groupNode?_ref found] using active)
            · exact output
  cases found : queue.taskNode? occurrence with
  | none => simp [State.taskFailure, found] at emitted
  | some task =>
      rw [queue.taskFailure_eq occurrence errors task found] at emitted
      split at emitted
      · cases emitted
      apply loop task.task.groups (queue.removeTask occurrence, []) ?_ (by simp) group
        count emitted
      intro node member active
      obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
      exact known old oldMember active

/-- An immediate failed closure counts the new task and all prior failures exactly.
Witness: its active group had an empty cache and hence zero contribution from the entire
earlier inventory; source ownership adds precisely the new fixed count.
No claim that all previously failed owners have retired is needed.
-/
theorem State.GroupErrorAccounting.taskFailure_output {queue : State} {work failed}
    (counts : queue.GroupErrorAccounting work failed)
    (clear : queue.NoActiveCachedFailure) (registered : queue.StartedTasksRegistered)
    (matching : queue.RegisteredTasksMatch work) (occurrence : Occurrence) (errors : Nat)
    (source : (GraphEvent.taskFailure occurrence errors).MatchesWork work) {group count}
    (emitted
      : Execution.WorkQueueEvent.groupFailure group count
        ∈ (queue.taskFailure occurrence errors).2)
    : NodeErrors work (occurrence :: failed) group.ref count := by
  have prior :=
    State.taskFailure_groupFailure_activeProperty
      (fun ref => NodeErrors work failed ref 0)
      (fun node member active => by
        simpa only [clear node member active, Option.getD_none]
          using counts.live node member)
      occurrence errors emitted
  obtain ⟨task, found, contributes, rfl⟩ :=
    queue.taskFailure_groupFailure_current occurrence errors emitted
  have member := registered task (List.mem_of_find?_eq_some found)
  obtain ⟨⟨_, _, _, _, descriptor⟩, _⟩ := matching task.task member
  rw [(State.taskNode?_some found).2] at descriptor
  obtain ⟨owners, producer, path, known⟩ := source
  have owner : group.ref ∈ owners := (descriptor.unique known).1 ▸ contributes
  simpa [owner, Payload.failure] using nodeErrors_cons prior known

-----------------------------------------------------------------------------------------
-- Every handler reports full totals; replay supplies the required state facts
-----------------------------------------------------------------------------------------

/-- Every raw failed-group output counts the eligible object-failure prefix through its input.
Witness: immediate failures use clear active caches; successful task/item handlers release
the exact full prior cache. Stream completion handlers cannot emit group failures.
-/
theorem State.GroupErrorAccounting.handleGraphEvent_output {queue : State} {work failed}
    (counts : queue.GroupErrorAccounting work failed)
    (clear : queue.NoActiveCachedFailure) (registered : queue.StartedTasksRegistered)
    (matching : queue.RegisteredTasksMatch work) (event : GraphEvent)
    (source : event.MatchesWork work) {group errors}
    (emitted
      : Execution.WorkQueueEvent.groupFailure group errors
        ∈ (queue.handleGraphEvent event).2)
    : NodeErrors work (queue.objectFailureContribution event ++ failed) group.ref
        errors := by
  cases event with
  | taskSuccess occurrence result =>
      exact counts.taskSuccess_output occurrence result emitted
  | taskFailure occurrence errors =>
      dsimp only [State.handleGraphEvent] at emitted
      obtain ⟨task, found, eligible⟩ := State.taskFailure_output_hasHealthyOwner
        (queue := queue) (occurrence := occurrence) (errors := errors)
        (fun empty => by rw [empty] at emitted; cases emitted)
      simpa only [State.objectFailureContribution, found, eligible, ↓reduceIte,
        List.singleton_append]
        using counts.taskFailure_output clear registered matching occurrence errors source
          emitted
  | streamItems stream items => exact counts.streamItems_output stream items emitted
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess] at emitted
      split at emitted <;> simp at emitted
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure] at emitted
      split at emitted <;> simp at emitted

/-- Any next matching handler reports the complete failure total after actual started replay.
Witness: replay derives cache totals, registration, and the no-active-cache invariant.
Completeness uses the guard-filtered ledger, not a separately selected list per completion.
Output-position transport and failure-cut licensing remain separate obligations.
-/
theorem ExecutedWork.runNormalized_groupFailure_nodeErrors {work : Execution.Work}
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true) (event : GraphEvent)
    (source : event.MatchesWork work) {group errors}
    (emitted
      : Execution.WorkQueueEvent.groupFailure group errors
        ∈ (((State.initialize (Work.fromExecution work)).runNormalized
              batches).1.handleGraphEvent
            event).2)
    : NodeErrors work
        (State.objectFailureContribution
            ((State.initialize (Work.fromExecution work)).runNormalized batches).1 event
          ++ (State.initialize (Work.fromExecution work)).objectFailureContributions
              batches.flatten)
        group.ref errors := by
  have counts := generated.runNormalized_groupErrorAccounting batches valid started
  have ledger := generated.runNormalized_pendingLedger batches valid started
  have clear := createWorkQueue_runNormalized_noActiveCachedFailure (Work.fromExecution work) batches
  exact counts.handleGraphEvent_output clear ledger.started ledger.matching event source emitted

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
