import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CachedFailureOutput
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InputReplay

/-! Retained causes are exact earlier contributing source rejections. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Selected causes record actual source rejections
-----------------------------------------------------------------------------------------

/-- A selected group cause is the exact count of one contributing source rejection.
This existential is proof evidence about input history; execution stores only the task's
rejected computation and selects it in registration order.
-/
def GroupFailureSourceCause (work : Execution.Work) (inputs : List GraphEvent)
    (ref : NodeRef) (errors : Nat)
    : Prop :=
  ∃ occurrence,
    GraphEvent.taskFailure occurrence errors ∈ inputs
    ∧ ∃ owners producer path,
        TaskAt work occurrence owners producer (.object path (.error errors))
        ∧ ref ∈ owners

/-- Extending input history preserves each selected source explanation. -/
theorem GroupFailureSourceCause.weaken {work before after ref errors}
    (cause : GroupFailureSourceCause work before ref errors)
    (included : before.Subset after)
    : GroupFailureSourceCause work after ref errors := by
  obtain ⟨occurrence, member, known⟩ := cause
  exact ⟨occurrence, included member, known⟩

/-- One matching rejected task certifies the same selected cause for each owner. -/
theorem GroupFailureSourceCause.single
    {work inputs ref occurrence errors owners producer path}
    (source : GraphEvent.taskFailure occurrence errors ∈ inputs)
    (known : TaskAt work occurrence owners producer (.object path (.error errors)))
    (owner : ref ∈ owners)
    : GroupFailureSourceCause work inputs ref errors :=
  ⟨occurrence, source, owners, producer, path, known, owner⟩

/-- A sole source failure fixes the selected count without aggregation. -/
theorem GroupFailureSourceCause.singleton_count {work ref count occurrence errors}
    (cause : GroupFailureSourceCause work [.taskFailure occurrence errors] ref count)
    : count = errors := by
  obtain ⟨task, member, _⟩ := cause
  exact (GraphEvent.taskFailure.inj (List.mem_singleton.mp member)).2

-----------------------------------------------------------------------------------------
-- One graph-event step maintains exact source causes
-----------------------------------------------------------------------------------------

/-- Surviving rejected tasks retain an exact matching source cause.
Witness: registration identifies the incoming task's contributors; every other rejection
keeps its earlier source witness.
-/
theorem State.CachedErrorsSatisfy.taskFailure_totals {queue : State} {work before}
    (totals : queue.CachedErrorsSatisfy (GroupFailureSourceCause work before))
    (_generated : ExecutedWork work) (registered : queue.StartedTasksRegistered)
    (matching : queue.RegisteredTasksMatch work) (occurrence : Occurrence) (errors : Nat)
    (source : (GraphEvent.taskFailure occurrence errors).MatchesWork work)
    (_fresh : (GraphEvent.taskFailure occurrence errors).Fresh before)
    : (queue.taskFailure occurrence errors).1.CachedErrorsSatisfy
        (GroupFailureSourceCause work (before ++ [.taskFailure occurrence errors])) := by
  have extended := totals.mono (fun _ _ total =>
    total.weaken (List.subset_append_left before [.taskFailure occurrence errors]))
  apply extended.taskFailure occurrence errors
  intro task found group member
  have registeredTask := registered task (List.mem_of_find?_eq_some found)
  have atTask := (State.taskNode?_some found).2
  obtain ⟨⟨_, _, _, _, known⟩, _⟩ := matching task.task registeredTask
  rw [atTask] at known
  obtain ⟨owners, producer, path, failed⟩ := source
  exact GroupFailureSourceCause.single (by simp) failed
    ((known.unique failed).1 ▸ List.mem_map.mpr ⟨group, member, rfl⟩)

/-- Every handler preserves exact source causes through a fresh matching input event.
Witness: only task failure adds a contribution; all other handlers preserve exact caches.
-/
theorem State.CachedErrorsSatisfy.handleGraphEvent_totals {queue : State} {work before}
    (totals : queue.CachedErrorsSatisfy (GroupFailureSourceCause work before))
    (generated : ExecutedWork work) (registered : queue.StartedTasksRegistered)
    (matching : queue.RegisteredTasksMatch work) (event : GraphEvent)
    (source : event.MatchesWork work) (fresh : event.Fresh before)
    : (queue.handleGraphEvent event).1.CachedErrorsSatisfy
        (GroupFailureSourceCause work (before ++ [event])) := by
  have extended := totals.mono (fun _ _ total =>
    total.weaken (List.subset_append_left before [event]))
  cases event with
  | taskSuccess occurrence result => exact extended.taskSuccess occurrence result
  | taskFailure occurrence errors =>
      exact totals.taskFailure_totals generated registered matching occurrence errors source fresh
  | streamItems stream items => exact extended.streamItems stream items
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> exact extended
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> exact extended

-----------------------------------------------------------------------------------------
-- Eventwise and normalized replay supply the invariant, without output admission
-----------------------------------------------------------------------------------------

/-- Source replay carries registration alongside its distinct-failure cache totals.
Witness: source-prefix induction threads registration and exact task causes together.
Neither accepted starts nor scheduler conformance is required for this direction.
-/
private theorem ExecutedWork.replayGraphEvents_failureInventory {work : Execution.Work}
    (generated : ExecutedWork work) {events : List GraphEvent}
    (valid : ValidGraphEvents work events)
    : let queue := (State.initialize (Work.fromExecution work)).replayGraphEvents events
      queue.CachedErrorsSatisfy (GroupFailureSourceCause work events)
      ∧ queue.StartedTasksRegistered
      ∧ queue.RegisteredTasksMatch work := by
  induction valid with
  | nil =>
      exact ⟨createWorkQueue_cachedErrors _ _, createWorkQueue_startedTasksRegistered _,
        createWorkQueue_fromSpec_registeredTasksMatch work⟩
  | @append before event valid matching fresh ready ih =>
      rw [State.replayGraphEvents_append]
      exact ⟨ih.1.handleGraphEvent_totals generated ih.2.1 ih.2.2 event matching fresh,
        ih.2.1.handleGraphEvent event, ih.2.2.handleGraphEvent event matching⟩

/-- Every cache after a valid source prefix retains a matching earlier owning-task rejection.
Witness: the joint replay inventory supplies exact totals and proves its own registration
premises internally. No accepted-start, output-admission, or conformance premise is used.
-/
theorem ExecutedWork.replayGraphEvents_cachedFailureTotals {work : Execution.Work}
    (generated : ExecutedWork work) {events : List GraphEvent}
    (valid : ValidGraphEvents work events)
    : ((State.initialize (Work.fromExecution work)).replayGraphEvents
        events).CachedErrorsSatisfy
        (GroupFailureSourceCause work events) :=
  (generated.replayGraphEvents_failureInventory valid).1

/-- Accepted normalized replay retains the same exact failure-total certificate.
Witness: normalization and batch termination affect no group cache in the eventwise state.
-/
theorem ExecutedWork.runNormalized_cachedFailureTotals {work : Execution.Work}
    (generated : ExecutedWork work) {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    : ((State.initialize (Work.fromExecution work)).runNormalized
        batches).1.CachedErrorsSatisfy
        (GroupFailureSourceCause work batches.flatten) := by
  obtain ⟨terminal, same⟩ := createWorkQueue_runNormalized_stateCore started
  rw [same]
  exact generated.replayGraphEvents_cachedFailureTotals valid

/-- Every failed closure uses the current failed input or a certified earlier total.
Witness: the handler origin theorem and registered task descriptors identify the current
contribution; exact caches cover closures released by a later successful input.
-/
theorem State.CachedErrorsSatisfy.handleGraphEvent_outputTotal {queue : State}
    {work before}
    (totals : queue.CachedErrorsSatisfy (GroupFailureSourceCause work before))
    (registered : queue.StartedTasksRegistered) (tasks : queue.RegisteredTasksMatch work)
    (event : GraphEvent) (matching : event.MatchesWork work) {group errors}
    (emitted
      : Execution.WorkQueueEvent.groupFailure group errors
        ∈ (queue.handleGraphEvent event).2)
    : GroupFailureSourceCause work (before ++ [event]) group.ref errors := by
  rcases queue.handleGraphEvent_groupFailure_origin event emitted with current | cached
  · obtain ⟨occurrence, task, rfl, found, owner⟩ := current
    have atTask := (State.taskNode?_some found).2
    obtain ⟨⟨_, _, _, _, known⟩, _⟩ := tasks task.task
      (registered task (List.mem_of_find?_eq_some found))
    rw [atTask] at known
    obtain ⟨owners, producer, path, failed⟩ := matching
    exact GroupFailureSourceCause.single (by simp) failed ((known.unique failed).1 ▸ owner)
  · obtain ⟨node, live, owner, contributes, ref, rejected⟩ := cached
    have total := totals node live errors rejected owner contributes
    rw [ref] at total
    exact total.weaken (List.subset_append_left before _)

/-- A failed closure after source replay reports a selected count from a contributing source rejection.
Witness: the handler's current-task-or-prior-cache origin, with exact replay totals in the
cached branch. This is payload provenance, not an ordered output failure-cut witness.
-/
theorem ExecutedWork.replayGraphEvents_groupFailureTotal {work : Execution.Work}
    (generated : ExecutedWork work) {before : List GraphEvent}
    (valid : ValidGraphEvents work before) (event : GraphEvent)
    (matching : event.MatchesWork work) {group errors}
    (emitted
      : Execution.WorkQueueEvent.groupFailure group errors
        ∈ (State.handleGraphEvent
            ((State.initialize (Work.fromExecution work)).replayGraphEvents before)
            event).2)
    : GroupFailureSourceCause work (before ++ [event]) group.ref errors := by
  obtain ⟨totals, registered, tasks⟩ := generated.replayGraphEvents_failureInventory valid
  exact totals.handleGraphEvent_outputTotal registered tasks event matching emitted

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
