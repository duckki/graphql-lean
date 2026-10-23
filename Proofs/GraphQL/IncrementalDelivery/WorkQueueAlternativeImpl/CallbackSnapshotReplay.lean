import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FailureCacheReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RetiredFailureSnapshot

/-! Concrete batch folds with a fixed host availability snapshot. Snapshot pruning removes
only globally retired occurrences; output and deferred startup notices remain exact.
-/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open WorkQueueSemantics (Occurrence)
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)

/-- Proof-facing name for the actual queue and emitted-output accumulator. -/
abbrev GraphSnapshotResult := State × List WorkQueueEvent

/-- The literal per-input fold step inside reference batch dispatch. -/
def graphSnapshotStep (available : List (Occurrence × Nat))
    (acc : GraphSnapshotResult) (event : GraphEvent)
    : GraphSnapshotResult :=
  let next := acc.1.dispatchGraphEvent event available
  (next.1, acc.2 ++ next.2)

/-- Dropping an irrelevant retired cache entry preserves realized enqueue effects. -/
theorem State.RetiredTask.dispatchGraphEvent_dropFailure {queue occurrence event}
    (retired : State.RetiredTask queue occurrence)
    (fresh : ∀ child ∈ event.childTasks, occurrence ≠ child.occurrence)
    (before after : List (Occurrence × Nat)) (errors : Nat)
    : queue.dispatchGraphEvent event (before ++ (occurrence, errors) :: after)
      = queue.dispatchGraphEvent event (before ++ after) := by
  simp only [State.dispatchGraphEvent, retired.handleGraphEvent_dropFailure fresh before after errors]

/-- A selected consumed failure retains its count through any source-valid suffix. -/
theorem State.replayGraphEvents_failureCached_of_mem (queue : State)
    {work before occurrence errors} (events : List GraphEvent)
    (valid : ValidGraphEvents work (before ++ events))
    (member : GraphEvent.taskFailure occurrence errors ∈ events)
    {available : List (Occurrence × Nat)}
    (known : FailureInSnapshot available occurrence errors)
    : (queue.replayGraphEvents events available).FailureCached occurrence errors := by
  induction events generalizing queue before with
  | nil => cases member
  | cons event rest ih =>
      have first : (before ++ [event]).IsPrefix (before ++ event :: rest) := ⟨rest, by simp⟩
      obtain ⟨priorValid, matching, fresh⟩ := validGraphEvents_last (valid.prefix first)
      have tailValid : ValidGraphEvents work ((before ++ [event]) ++ rest) := by
        simpa only [List.append_assoc, List.singleton_append] using valid
      rcases List.mem_cons.mp member with same | later
      · subst event
        have completed : (queue.dispatchGraphEvent (.taskFailure occurrence errors)
            available).1.FailureCached occurrence errors :=
          (queue.cacheTaskFailures available).taskFailure_failureCached occurrence errors
        exact completed.replayGraphEvents matching
          (by simp [List.flatMap_append, GraphEvent.identities]) rest tailValid known
      · exact ih _ tailValid later

/-- A completed batch stabilizes any consistent snapshot drawn from its own failures.
The snapshot may omit retired callbacks whose causes were irrelevant throughout the batch.
-/
theorem State.TaskNodeKeysUnique.replayGraphEvents_cache_subset_fixed {queue : State}
    (unique : queue.TaskNodeKeysUnique) {work before} (events : List GraphEvent)
    (valid : ValidGraphEvents work (before ++ events))
    (available : List (Occurrence × Nat))
    (included : available.Subset (GraphEvent.availableFailures events))
    : (queue.replayGraphEvents events available).cacheTaskFailures available
      = queue.replayGraphEvents events available := by
  apply (unique.replayGraphEvents events available).cacheTaskFailures_eq_self
  intro entry member
  have input (candidate : Occurrence × Nat) (received : candidate ∈ available)
      : GraphEvent.taskFailure candidate.1 candidate.2 ∈ events := by
    obtain ⟨event, present, same⟩ := List.mem_filterMap.mp (included received)
    cases event <;> simp only [Option.some.injEq, reduceCtorEq] at same
    obtain ⟨rfl, rfl⟩ := same
    exact present
  apply queue.replayGraphEvents_failureCached_of_mem events valid (input entry member)
  apply FailureInSnapshot.of_mem member
  intro other received same
  have left := valid.eachMatches (List.mem_append_right _ (input other received))
  rw [same] at left
  exact left.taskFailure_count_unique
    (valid.eachMatches (List.mem_append_right _ (input entry member)))

/-- Dropping a retired failure from availability preserves the entire raw dispatch fold. -/
theorem State.RetiredTask.fold_dropFailure {acc : GraphSnapshotResult} {occurrence}
    (retired : acc.1.RetiredTask occurrence) (events : List GraphEvent)
    (fresh : ∀ event ∈ events, ∀ task ∈ event.childTasks, occurrence ≠ task.occurrence)
    (before after : List (Occurrence × Nat)) (errors : Nat)
    : events.foldl (graphSnapshotStep (before ++ (occurrence, errors) :: after)) acc
      = events.foldl (graphSnapshotStep (before ++ after)) acc := by
  induction events generalizing acc with
  | nil => rfl
  | cons event rest ih =>
      have next := retired.dispatchGraphEvent_dropFailure (fresh event List.mem_cons_self)
        before after errors
      simp only [List.foldl_cons, graphSnapshotStep, next]
      exact ih (retired.dispatchGraphEvent (fresh event List.mem_cons_self) (before ++ after))
        (fun current member => fresh current (List.mem_cons_of_mem _ member))

/-- Filtering globally retired causes preserves exact queue and output accumulation.
Fresh child-work identities are structural premises, not desired output equivalence.
-/
theorem graphSnapshotStep_filterFailures (acc : GraphSnapshotResult)
    (events : List GraphEvent) (available : List (Occurrence × Nat))
    (keep : Occurrence × Nat → Bool)
    (retired : ∀ entry ∈ available, keep entry = false → acc.1.RetiredTask entry.1)
    (fresh
      : ∀ entry ∈ available,
          keep entry = false
          → ∀ event ∈ events, ∀ task ∈ event.childTasks, entry.1 ≠ task.occurrence)
    : events.foldl (graphSnapshotStep available) acc
      = events.foldl (graphSnapshotStep (available.filter keep)) acc := by
  have loop (remaining : List (Occurrence × Nat)) (included : remaining.Subset available)
      (earlier : List (Occurrence × Nat))
      : events.foldl (graphSnapshotStep (earlier ++ remaining)) acc
        = events.foldl (graphSnapshotStep (earlier ++ remaining.filter keep)) acc := by
    induction remaining generalizing earlier with
    | nil => rfl
    | cons entry rest ih =>
        cases kept : keep entry with
        | true =>
            simpa only [List.filter_cons, kept, ↓reduceIte, List.append_assoc,
              List.singleton_append] using ih
                (fun next member => included (List.mem_cons_of_mem _ member)) (earlier ++ [entry])
        | false =>
            rw [(retired entry (included List.mem_cons_self) kept).fold_dropFailure events
              (fresh entry (included List.mem_cons_self) kept) earlier rest entry.2]
            simpa only [List.filter_cons, kept, Bool.false_eq_true, ↓reduceIte]
              using ih (fun next member => included (List.mem_cons_of_mem _ member))
                earlier
  exact loop available (List.Subset.refl _) []

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
