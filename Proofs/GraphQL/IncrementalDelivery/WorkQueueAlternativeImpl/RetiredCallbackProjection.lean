import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.CallbackSnapshotReplay

/-! Removing callbacks retired before a batch begins. Within-batch retirement is deliberately
excluded: those callbacks retain their original failure availability and source permission.
-/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open WorkQueueSemantics (Occurrence)

/-- Object computation identity carried by a task notification, excluding stream receipts. -/
def GraphEvent.taskCallback? : GraphEvent → Option Occurrence
  | .taskSuccess occurrence _ | .taskFailure occurrence _ => some occurrence
  | _ => none

/-- A globally retired task callback only repeats cache exposure; it emits no output. -/
theorem State.RetiredTask.handleGraphEvent_retired {queue occurrence}
    (retired : State.RetiredTask queue occurrence) (event : GraphEvent)
    (same : event.taskCallback? = some occurrence) (available : List (Occurrence × Nat))
    : queue.handleGraphEvent event available
      = (queue.cacheTaskFailures available, [], []) := by
  have cached := retired.cacheTaskFailures available
  cases event <;> simp only [GraphEvent.taskCallback?, Option.some.injEq, reduceCtorEq] at same
  all_goals subst same
  · simp only [State.handleGraphEvent, State.taskSuccess, cached.missing]
  · simp only [State.handleGraphEvent, State.taskFailure, cached.missing]

/-- A retired notification realizes no new effects and preserves the pending notice FIFO. -/
theorem State.RetiredTask.dispatchGraphEvent_retired {queue occurrence}
    (retired : State.RetiredTask queue occurrence) (event : GraphEvent)
    (same : event.taskCallback? = some occurrence) (available : List (Occurrence × Nat))
    : queue.dispatchGraphEvent event available
      = (queue.cacheTaskFailures available, []) := by
  simp only [State.dispatchGraphEvent, retired.handleGraphEvent_retired event same available,
    State.enqueueGroupFailures, List.append_nil]

private def exposeSnapshot (available : List (Occurrence × Nat))
    (result : GraphSnapshotResult)
    : GraphSnapshotResult :=
  (result.1.cacheTaskFailures available, result.2)

private theorem filter_exposed (events : List GraphEvent) (keep : GraphEvent → Bool)
    (retiredOccurrences : List Occurrence) (available : List (Occurrence × Nat))
    (left right : GraphSnapshotResult)
    (same : exposeSnapshot available left = exposeSnapshot available right)
    (unique : left.1.TaskNodeKeysUnique)
    (retired : ∀ occurrence ∈ retiredOccurrences, left.1.RetiredTask occurrence)
    (dropped
      : ∀ event ∈ events,
          keep event = false
          → ∃ occurrence ∈ retiredOccurrences, event.taskCallback? = some occurrence)
    (fresh
      : ∀ occurrence ∈ retiredOccurrences,
        ∀ event ∈ events, ∀ task ∈ event.childTasks, occurrence ≠ task.occurrence)
    : exposeSnapshot available (events.foldl (graphSnapshotStep available) left)
      = exposeSnapshot available
          ((events.filter keep).foldl (graphSnapshotStep available) right) := by
  induction events generalizing left right with
  | nil => exact same
  | cons event rest ih =>
      have nextRetired : ∀ occurrence ∈ retiredOccurrences,
          (left.1.dispatchGraphEvent event available).1.RetiredTask occurrence := by
        intro occurrence member
        exact (retired occurrence member).dispatchGraphEvent
          (fresh occurrence member event List.mem_cons_self) available
      have laterDropped := fun current member => dropped current (List.mem_cons_of_mem _ member)
      have laterFresh := fun occurrence member current present =>
        fresh occurrence member current (List.mem_cons_of_mem _ present)
      cases kept : keep event with
      | true =>
          have exposed : left.1.cacheTaskFailures available = right.1.cacheTaskFailures available :=
            congrArg Prod.fst same
          have metadata := congrArg (fun result : GraphSnapshotResult => result.2) same
          change left.2 = right.2 at metadata
          have next : left.1.dispatchGraphEvent event available
              = right.1.dispatchGraphEvent event available := by
            simp only [State.dispatchGraphEvent, State.handleGraphEvent, exposed]
          have step : graphSnapshotStep available left event
              = graphSnapshotStep available right event := by
            simp only [graphSnapshotStep, next, metadata]
          simp only [List.foldl_cons, List.filter_cons, kept, ↓reduceIte]
          apply ih _ _ (congrArg (exposeSnapshot available) step)
            (unique.handleGraphEvent event available) nextRetired laterDropped laterFresh
      | false =>
          obtain ⟨occurrence, member, callback⟩ := dropped event List.mem_cons_self kept
          have ignored :=
            (retired occurrence member).dispatchGraphEvent_retired event callback available
          have step : exposeSnapshot available (graphSnapshotStep available left event)
              = exposeSnapshot available right := by
            simpa only [graphSnapshotStep, ignored, exposeSnapshot,
              unique.cacheTaskFailures_idempotent available, List.append_nil]
              using same
          simp only [List.foldl_cons, List.filter_cons, kept, Bool.false_eq_true, ↓reduceIte]
          exact ih _ _ step (unique.handleGraphEvent event available)
            nextRetired laterDropped laterFresh

/-- Retired callbacks can be removed from a source-valid batch without changing its exact
fold under the retained availability snapshot. Both raw and retained work laws are explicit;
callers derive them independently from enqueue histories and producer support.
-/
theorem graphSnapshotStep_filterRetiredEvents {work before retainedBefore}
    (queue : State) (events : List GraphEvent) (keep : GraphEvent → Bool)
    (retiredOccurrences : List Occurrence) (unique : queue.TaskNodeKeysUnique)
    (retired : ∀ occurrence ∈ retiredOccurrences, queue.RetiredTask occurrence)
    (dropped
      : ∀ event ∈ events,
          keep event = false
          → ∃ occurrence ∈ retiredOccurrences, event.taskCallback? = some occurrence)
    (fresh
      : ∀ occurrence ∈ retiredOccurrences,
        ∀ event ∈ events, ∀ task ∈ event.childTasks, occurrence ≠ task.occurrence)
    (valid : ValidGraphEvents work (before ++ events))
    (retained : ValidGraphEvents work (retainedBefore ++ events.filter keep))
    : let available := GraphEvent.availableFailures (events.filter keep)
      events.foldl (graphSnapshotStep available) (queue, [])
      = (events.filter keep).foldl (graphSnapshotStep available) (queue, []) := by
  let available := GraphEvent.availableFailures (events.filter keep)
  have exposed := filter_exposed events keep retiredOccurrences available (queue, [])
    (queue, []) rfl unique retired dropped fresh
  have left := unique.replayGraphEvents_cache_subset_fixed events valid available (by
    intro entry member
    obtain ⟨event, input, same⟩ := List.mem_filterMap.mp member
    exact List.mem_filterMap.mpr ⟨event, (List.mem_filter.mp input).1, same⟩)
  have right := unique.replayGraphEvents_cache_fixed (events.filter keep) retained
  have leftState := queue.foldGraphEvents_state [] events available
  have rightState := queue.foldGraphEvents_state [] (events.filter keep) available
  change (events.foldl (graphSnapshotStep available) (queue, [])).1
    = queue.replayGraphEvents events available at leftState
  change ((events.filter keep).foldl (graphSnapshotStep available) (queue, [])).1
    = queue.replayGraphEvents (events.filter keep) available at rightState
  have leftFixed : exposeSnapshot available
      (events.foldl (graphSnapshotStep available) (queue, []))
      = events.foldl (graphSnapshotStep available) (queue, []) := by
    unfold exposeSnapshot
    rw [leftState, left, ← leftState]
  have rightFixed : exposeSnapshot available
      ((events.filter keep).foldl (graphSnapshotStep available) (queue, []))
      = (events.filter keep).foldl (graphSnapshotStep available) (queue, []) := by
    unfold exposeSnapshot
    rw [rightState, right, ← rightState]
  exact leftFixed.symm.trans (exposed.trans rightFixed)

private theorem availableFailures_filter (events : List GraphEvent)
    (keep : GraphEvent → Bool)
    : GraphEvent.availableFailures (events.filter keep)
      = (GraphEvent.availableFailures events).filter
          (fun entry => keep (.taskFailure entry.1 entry.2)) := by
  induction events with
  | nil => rfl
  | cons event rest ih =>
      cases event <;> simp only [List.filter_cons, GraphEvent.availableFailures,
        List.filterMap_cons] <;> split <;> simp_all [GraphEvent.availableFailures]

/-- Removing callbacks already globally retired at batch entry preserves the complete
reference batch result, including deferred startup reports and terminal publication.
-/
theorem State.handleGraphEvents_filterRetired {work before retainedBefore}
    (queue : State) (events : List GraphEvent) (keep : GraphEvent → Bool)
    (retiredOccurrences : List Occurrence) (unique : queue.TaskNodeKeysUnique)
    (retired : ∀ occurrence ∈ retiredOccurrences, queue.RetiredTask occurrence)
    (dropped
      : ∀ event ∈ events,
          keep event = false
          → ∃ occurrence ∈ retiredOccurrences, event.taskCallback? = some occurrence)
    (fresh
      : ∀ occurrence ∈ retiredOccurrences,
        ∀ event ∈ events, ∀ task ∈ event.childTasks, occurrence ≠ task.occurrence)
    (valid : ValidGraphEvents work (before ++ events))
    (retained : ValidGraphEvents work (retainedBefore ++ events.filter keep))
    : queue.handleGraphEvents (events.filter keep) = queue.handleGraphEvents events := by
  let available := GraphEvent.availableFailures events
  let failureKeep := fun entry : Occurrence × Nat => keep (.taskFailure entry.1 entry.2)
  have prune := graphSnapshotStep_filterFailures (queue, []) events available failureKeep
    (by
      intro entry member discarded
      obtain ⟨event, received, same⟩ := List.mem_filterMap.mp member
      cases event <;> simp only [Option.some.injEq, reduceCtorEq] at same
      obtain ⟨rfl, rfl⟩ := same
      obtain ⟨occurrence, known, identity⟩ := dropped _ received discarded
      simp only [GraphEvent.taskCallback?, Option.some.injEq] at identity
      exact identity ▸ retired occurrence known)
    (by
      intro entry member discarded
      obtain ⟨event, received, same⟩ := List.mem_filterMap.mp member
      cases event <;> simp only [Option.some.injEq, reduceCtorEq] at same
      obtain ⟨rfl, rfl⟩ := same
      obtain ⟨occurrence, known, identity⟩ := dropped _ received discarded
      simp only [GraphEvent.taskCallback?, Option.some.injEq] at identity
      exact identity ▸ fresh occurrence known)
  have filtered := graphSnapshotStep_filterRetiredEvents queue events keep retiredOccurrences
    unique retired dropped fresh valid retained
  have sameAvailability : available.filter failureKeep
      = GraphEvent.availableFailures (events.filter keep) :=
    (availableFailures_filter events keep).symm
  rw [sameAvailability] at prune
  have folded := prune.trans filtered
  simp only [State.handleGraphEvents]
  split
  · rfl
  · have concrete := folded
    unfold graphSnapshotStep at concrete
    rw [concrete]

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
