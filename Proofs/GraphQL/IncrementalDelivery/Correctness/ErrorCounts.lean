import Proofs.GraphQL.IncrementalDelivery.Correctness.FailureCounts

/-! Every payload and completion error is conserved by work and response grouping. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open MapperIdentity

/-- All error counts carried by an individual work event. -/
def workEventErrors : WorkEvent → Nat
  | .groupValues _ values => (values.map GroupValue.errors).sum
  | .streamValues _ values _ _ => (values.map StreamValue.errors).sum
  | .groupFailure _ errors | .streamFailure _ errors => errors
  | _ => 0

/-- An update's complete error subtotal, including patches and completion notices. -/
def updateErrors (update : IncrementalStreamUpdateResult) : Nat :=
  (update.incremental.map IncrementalResult.errors).sum + completionErrors update

/-- Object-entry mapping retains each payload's error count, independently of IDs. -/
theorem incrementalEntries_errors (node : DeliveryNode) (values : List GroupValue)
    (ids : IDState)
    : (((values.mapM
          (fun value =>
            getIncrementalEntry (m := StateM IDState) node value ensureID)).run
          ids).1.map
        IncrementalResult.errors).sum
      = (values.map GroupValue.errors).sum := by
  induction values generalizing ids with
  | nil => rfl
  | cons value rest ih =>
      simp only [List.mapM_cons, getIncrementalEntry, StateT.run, StateT.bind,
        StateT.pure, bind, pure]
      split
      rename_i entries final found
      have tail := ih (ensureID node ids).2
      simp only [getIncrementalEntry, StateT.run, bind, pure] at tail
      rw [found] at tail
      simp [IncrementalResult.errors, tail]

/-- Each event adds exactly its full error count; witness: mapper cases and entry counts.
-/
theorem eventLoop_errors (event : WorkEvent)
    (initial update : IncrementalStreamUpdateResult) (ids next : IDState)
    (mapped : (eventLoop event initial).run ids = (.yield update, next))
    : updateErrors update = updateErrors initial + workEventErrors event := by
  cases event with
  | groupValues node values =>
      have counts := incrementalEntries_errors node values ids
      simp only [eventLoop, StateT.run, StateT.bind, StateT.pure, bind, pure] at mapped
      split at mapped
      rename_i entries state found
      simp only [StateT.run] at counts
      rw [found] at counts
      cases mapped
      simp [updateErrors, completionErrors, workEventErrors, counts, Nat.add_right_comm]
  | groupSuccess node groups streams | groupFailure node errors
  | streamValues node values groups streams | streamSuccess node
  | streamFailure node errors | workQueueTermination =>
      simp only [eventLoop, getCompletedEntry, StateT.run, StateT.bind,
        StateT.pure, bind, pure] at mapped
      all_goals
        repeat first | split at mapped | cases mapped
        simp [updateErrors, completionErrors, workEventErrors, IncrementalResult.errors,
          Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- Iteration preserves the sum of all supplied event error counts, by loop induction. -/
theorem loop_errors (events : List WorkEvent) (initial : IncrementalStreamUpdateResult)
    (ids : IDState)
    : updateErrors ((forIn events initial eventLoop).run ids).1
      = updateErrors initial + (events.map workEventErrors).sum := by
  induction events generalizing initial ids with
  | nil =>
      simp; rfl
  | cons event rest ih =>
      obtain ⟨middle, state, mapped, _⟩ := eventLoop_spec event initial ids
      have count := eventLoop_errors event initial middle ids state mapped
      have tail := ih middle state
      simp only [StateT.run] at mapped tail
      simp [List.forIn_cons, StateT.run, StateT.bind, bind, mapped, tail, count,
        Nat.add_assoc]

/-- Public event-batch mapping preserves the full error sum. -/
theorem mapWorkEventBatch_errors (events : List WorkEvent) (ids : IDState)
    : updateErrors ((mapWorkEventBatch events).run ids).1
      = (events.map workEventErrors).sum := by
  rw [mapWorkEventBatch_loop, loop_errors]
  simp [updateErrors, completionErrors]

/-- Mapping any finite sequence of supplied batches preserves its full error sum. -/
theorem mappedTrace_errors (batches : List (List WorkEvent)) (ids : IDState)
    : ((mappedTrace batches ids).map updateErrors).sum
      = (batches.flatten.map workEventErrors).sum := by
  induction batches generalizing ids with
  | nil => rfl
  | cons batch rest ih =>
      have count := mapWorkEventBatch_errors batch ids
      cases mapped : (mapWorkEventBatch batch).run ids with
      | mk update next =>
          simp only [mapped] at count
          simp only [mappedTrace, mapped, List.map_cons, List.sum_cons,
            List.flatten_cons, List.map_append, List.sum_append, ih, count]

/-- Response aggregation adds all error subtotals, by fold induction. -/
theorem combineFrom_errors (updates : List IncrementalStreamUpdateResult)
    (initial : IncrementalStreamUpdateResult)
    : updateErrors (combineFrom updates initial)
      = updateErrors initial + (updates.map updateErrors).sum := by
  induction updates generalizing initial with
  | nil => simp [combineFrom]
  | cons update rest ih =>
      simpa [combineFrom, updateErrors, completionErrors, Nat.add_assoc,
        Nat.add_left_comm, Nat.add_comm] using ih
        { hasNext := update.hasNext, pending := initial.pending ++ update.pending,
          incremental := initial.incremental ++ update.incremental,
          completed := initial.completed ++ update.completed }

/-- Public response coalescing retains the sum of all grouped error subtotals. -/
theorem combineIncrementalResults_errors (updates : List IncrementalStreamUpdateResult)
    : updateErrors (combineIncrementalResults updates)
      = (updates.map updateErrors).sum := by
  simpa [combineFrom, combineIncrementalResults, updateErrors, completionErrors]
    using combineFrom_errors updates { hasNext := false }

/-- Grouped response replay retains every error count, by group induction. -/
theorem batched_errors (groups : List (List IncrementalStreamUpdateResult))
    : ((groups.map combineIncrementalResults).map updateErrors).sum
      = (groups.flatten.map updateErrors).sum := by
  induction groups with
  | nil => rfl
  | cons group rest ih =>
      simp only [List.map_cons, List.sum_cons, List.flatten_cons, List.map_append,
        List.sum_append, combineIncrementalResults_errors, ih]

/-- The observed error total is the initial count plus all work-event errors, with
arbitrary supplied work and response groups. Witness: exact mapper and coalescing sums.
-/
theorem replayResponse_errors (response : Response)
    (initialGroups initialStreams : List DeliveryNode)
    (groups : List (List (List WorkEvent)))
    : (replayResponse response initialGroups initialStreams groups).totalErrors
      = response.errors + (groups.flatten.flatten.map workEventErrors).sum := by
  cases allocated
        : (getPendingEntry (m := StateM IDState) initialGroups initialStreams
            ensureID).run
            {} with
  | mk pending ids =>
      have replayed := replayResponse_groups response initialGroups initialStreams groups
      rw [allocated] at replayed
      obtain ⟨updates, flat, replay⟩ := replayed
      rw [replay]
      change response.errors + ((updates.map combineIncrementalResults).map
        updateErrors).sum = _
      rw [batched_errors, flat, mappedTrace_errors]

end GraphQL.IncrementalDelivery.Correctness
