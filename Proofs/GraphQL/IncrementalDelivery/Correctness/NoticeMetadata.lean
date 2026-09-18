import Proofs.GraphQL.IncrementalDelivery.Correctness.MapperMetadata
import Proofs.GraphQL.IncrementalDelivery.Correctness.WorkEventMetadata
import Proofs.GraphQL.IncrementalDelivery.Correctness.ResponseReplay

/-! Event mapping preserves the source paths of every announced wire ID. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open MapperIdentity

/-- One mapped event preserves old notice metadata and adds coherent new notices.
Witness: stable allocation plus the pending-entry metadata specification.
-/
theorem eventLoop_noticePaths {paths : Nat → ResponsePath} (event : WorkEvent)
    (initial update : IncrementalStreamUpdateResult) (ids next : IDState)
    (coherent : ∀ node ∈ eventNodes event, paths node.key = node.path)
    (valid : NoticePaths paths ids initial.pending)
    (mapped : (eventLoop event initial).run ids = (.yield update, next))
    : NoticePaths paths next update.pending := by
  have preserved : Preserves ids next := by
    obtain ⟨other, state, equal, facts⟩ := eventLoop_spec event initial ids
    have same : other = update ∧ state = next := by
      have same := equal.symm.trans mapped
      injection same with output states
      injection output with outputs
      exact ⟨outputs, states⟩
    rcases same with ⟨rfl, rfl⟩
    exact facts.preserves
  have previous := valid.mono preserved
  cases event with
  | groupValues node values | groupFailure node errors | streamSuccess node
  | streamFailure node errors | workQueueTermination =>
      simp only [eventLoop, StateT.run, StateT.bind, StateT.pure, bind, pure] at mapped
      all_goals
        repeat first | split at mapped | cases mapped
        exact previous
  | groupSuccess node groups streams =>
      cases completed
            : (getCompletedEntry (m := StateM IDState) node 0 ensureID).run ids with
      | mk entry middle =>
          cases pending
                : (getPendingEntry (m := StateM IDState) groups streams ensureID).run
                    middle with
          | mk notices final =>
              have fresh := (getPendingEntry_metadata_of_eq pending).paths
                (fun node member => coherent node (List.mem_cons_of_mem _ member))
              simp only [StateT.run] at completed pending
              simp only [eventLoop, StateT.run, StateT.bind, StateT.pure, bind, pure,
                completed, pending] at mapped
              cases mapped
              exact previous.append fresh
  | streamValues node values groups streams =>
      cases allocated : ensureID node ids with
      | mk id middle =>
          cases pending
                : (getPendingEntry (m := StateM IDState) groups streams ensureID).run
                    middle with
          | mk notices final =>
              have fresh := (getPendingEntry_metadata_of_eq pending).paths
                (fun node member => coherent node (List.mem_cons_of_mem _ member))
              simp only [StateT.run] at pending
              simp only [eventLoop, StateT.run, StateT.bind, StateT.pure, bind, pure,
                allocated, pending] at mapped
              cases mapped
              exact previous.append fresh

/-- Mapping an event prefix retains metadata for every accumulated notice, by loop
induction. Descriptors are assumed coherent, not lifecycle-valid or successfully merged.
-/
theorem loop_noticePaths {paths : Nat → ResponsePath} (events : List WorkEvent)
    (initial : IncrementalStreamUpdateResult) (ids : IDState)
    (coherent : ∀ node ∈ events.flatMap eventNodes, paths node.key = node.path)
    (valid : NoticePaths paths ids initial.pending)
    : NoticePaths paths ((forIn events initial eventLoop).run ids).2
        ((forIn events initial eventLoop).run ids).1.pending := by
  induction events generalizing initial ids with
  | nil => exact valid
  | cons event rest ih =>
      obtain ⟨middle, next, mapped, _⟩ := eventLoop_spec event initial ids
      have current := eventLoop_noticePaths event initial middle ids next
        (fun node member => coherent node (List.mem_append_left _ member)) valid mapped
      have tail := ih middle next
        (fun node member => coherent node (List.mem_append_right _ member)) current
      simp only [StateT.run] at mapped tail
      simpa [List.forIn_cons, StateT.run, StateT.bind, bind, mapped] using tail

/-- Public batch mapping retains every pending notice's source path, by the loop rule.
-/
theorem mapWorkEventBatch_noticePaths {paths : Nat → ResponsePath}
    (events : List WorkEvent) (ids : IDState)
    (coherent : ∀ node ∈ events.flatMap eventNodes, paths node.key = node.path)
    : NoticePaths paths ((mapWorkEventBatch events).run ids).2
        ((mapWorkEventBatch events).run ids).1.pending := by
  rw [mapWorkEventBatch_loop]
  exact loop_noticePaths events { hasNext := true } ids coherent (by simp [NoticePaths])

/-- All notices in a finite observed replay retain source paths in its final ID state.
Witness: batch induction and allocation stability through the remaining supplied inputs.
-/
theorem mappedTrace_noticePaths {paths : Nat → ResponsePath}
    (batches : List (List WorkEvent)) (ids : IDState)
    (coherent : ∀ node ∈ batches.flatten.flatMap eventNodes, paths node.key = node.path)
    : NoticePaths paths (finalIDs batches ids)
        ((mappedTrace batches ids).flatMap IncrementalStreamUpdateResult.pending) := by
  induction batches generalizing ids with
  | nil => simp [mappedTrace, NoticePaths]
  | cons batch rest ih =>
      have head := mapWorkEventBatch_noticePaths batch ids
        (fun node member => coherent node (by
          simp only [List.flatten_cons, List.flatMap_append]
          exact List.mem_append_left _ member))
      cases mapped : (mapWorkEventBatch batch).run ids with
      | mk update next =>
          simp only [mapped] at head
          have tail := ih next (fun node member => coherent node (by
            simp only [List.flatten_cons, List.flatMap_append]
            exact List.mem_append_right _ member))
          simpa only [mappedTrace, finalIDs, mapped, List.flatMap_cons]
            using (head.mono (mappedTrace_spec rest next).1).append tail

/-- Response coalescing concatenates the actual pending notices, not only their IDs;
witness: fold induction preserves paths and labels as well.
-/
theorem combineFrom_pending (updates : List IncrementalStreamUpdateResult)
    (initial : IncrementalStreamUpdateResult)
    : (combineFrom updates initial).pending
      = initial.pending ++ updates.flatMap IncrementalStreamUpdateResult.pending := by
  induction updates generalizing initial with
  | nil => simp [combineFrom]
  | cons update rest ih =>
      simpa [combineFrom, List.append_assoc] using ih
        { hasNext := update.hasNext, pending := initial.pending ++ update.pending,
          incremental := initial.incremental ++ update.incremental,
          completed := initial.completed ++ update.completed }

/-- Arbitrary response coalescing preserves the ordered pending descriptors. -/
theorem batched_pending (groups : List (List IncrementalStreamUpdateResult))
    : (groups.map combineIncrementalResults).flatMap IncrementalStreamUpdateResult.pending
      = groups.flatten.flatMap IncrementalStreamUpdateResult.pending := by
  have one (updates : List IncrementalStreamUpdateResult)
      : (combineIncrementalResults updates).pending
        = updates.flatMap IncrementalStreamUpdateResult.pending := by
    simpa only [combineFrom, combineIncrementalResults, List.nil_append]
      using combineFrom_pending updates { hasNext := false }
  induction groups with
  | nil => rfl
  | cons group rest ih =>
      simp only [List.map_cons, List.flatMap_cons, List.flatten_cons, List.flatMap_append,
        one, ih]

/-- All pending notices actually present in a finite observed result. -/
def queryNotices : QueryResult → List IncrementalPendingNotice
  | .single _ => []
  | .incremental initial updates =>
      initial.pending ++ updates.flatMap IncrementalStreamUpdateResult.pending

/-- Every notice in an admitted work observation has its generated source path and a
stable injective ID. Witness: structural descriptor provenance, mapper metadata, and
exact preservation through response coalescing. No future source inputs are selected.
-/
theorem WorkObservation.noticePaths {paths bound response work complete result}
    (observed : WorkObservation response work complete result)
    (coherent : Semantics.MixedOwnerPaths.WorkAt paths bound work)
    : ∃ ids, Allocated ids ∧ NoticePaths paths ids (queryNotices result) := by
  cases observed with
  | single _ => exact ⟨{}, .empty, by simp [queryNotices, NoticePaths]⟩
  | incremental groups streams batches _ _ admitted _ =>
      obtain ⟨initialPaths, eventPaths⟩ := history_node_paths coherent admitted
      cases allocated
            : (getPendingEntry (m := StateM IDState) groups streams ensureID).run {} with
      | mk pending ids =>
          have valid := (getPendingEntry_metadata_of_eq allocated).paths initialPaths
          have well := getPendingEntry_allocated groups streams {} Allocated.empty
          simp only [allocated] at well
          have finalWell := finalIDs_allocated batches.flatten ids well
          have initial := valid.mono (mappedTrace_spec batches.flatten ids).1
          have subsequent := mappedTrace_noticePaths batches.flatten ids eventPaths
          have replayed := replayResponse_groups response groups streams batches
          rw [allocated] at replayed
          obtain ⟨updates, flat, replay⟩ := replayed
          rw [replay, queryNotices, batched_pending, flat]
          exact ⟨_, finalWell, initial.append subsequent⟩

end GraphQL.IncrementalDelivery.Correctness
