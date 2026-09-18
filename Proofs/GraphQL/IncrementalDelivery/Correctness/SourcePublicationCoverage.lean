import Proofs.GraphQL.IncrementalDelivery.Correctness.HistoryAbsolutePositions
import Proofs.GraphQL.IncrementalDelivery.Correctness.PublicationCoverage

/-! Complete successful histories publish exactly the structural source inventory. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open WorkScheduler
open Semantics.MixedPaths

/-- A matched publication inserts its source label into every later observed prefix.
Witness: prefix induction and the inventory's unique occurrence lookup.
-/
theorem sourcePrefixTasks_of_publication {initial work matching events task index event}
    (member : task ∈ sourceTasks [] none initial work)
    (selected : events[index]? = some event) (value : IsValue event)
    (same : task.occurrence = matching index) {cut : Nat} (before : index < cut)
    : task
      ∈ sourcePrefixTasks (sourceTasks [] none initial work) matching events cut := by
  induction cut with
  | zero => omega
  | succ cut ih =>
      rw [sourcePrefixTasks, List.mem_append]
      by_cases equal : index = cut
      · subst index
        exact Or.inr (by simp [selected, sourceEventTask_value value member same])
      · exact Or.inl (ih (by omega))

/-- A complete successful publication history permutes the whole source inventory.
Witness: terminal task coverage supplies membership in both directions, while one-shot
publication and structural occurrence uniqueness exclude duplicates.
-/
theorem sourcePrefixTasks_perm {work groups streams events matching failures initial}
    (explained : Explains work groups streams events matching failures)
    (complete
      : ∀ occurrence owners producer payload,
          TaskAt work occurrence owners producer payload
          → Published matching events occurrence)
    : (sourcePrefixTasks (sourceTasks [] none initial work) matching events
        events.length).Perm
        (sourceTasks [] none initial work) := by
  have selectedUnique := (sourcePrefixTasks_unique explained
    (sourceTasks [] none initial work) events.length).imp
    (fun different equal => different (congrArg SourceTask.occurrence equal))
  have inventoryUnique := (sourceTasks_unique [] none initial work).imp
    (fun different equal => different (congrArg SourceTask.occurrence equal))
  apply (List.perm_ext_iff_of_nodup selectedUnique inventoryUnique).mpr
  intro task
  constructor
  · exact fun member => (sourcePrefixTasks_member member).1
  · intro member
    obtain ⟨owners, known⟩ := sourceTasks_known .root initial member
    obtain ⟨index, event, selected, value, same⟩ :=
      complete task.occurrence owners task.producer task.payload known
    exact sourcePrefixTasks_of_publication member selected value same.symm
      (List.getElem?_eq_some_iff.mp selected).choose

/-- A successful complete replay decodes every source position exactly once, up to
publication order, with or without container positions. Witness: failure-free terminal
coverage, the exact history decoder, and batching's ordered atom preservation.
-/
theorem replayResponse_absolute_coverage
    {paths bound response work groups streams batches initial slices positions}
    (coherent : Semantics.MixedOwnerPaths.WorkAt paths bound work)
    (positive : ExecutionErrors.WorkPositive work)
    (seeded : WorkCursorSeed initial work slices)
    (initialHistory : CursorHistory initial positions)
    (disjoint
      : (positions
          ++ (sourceTasks [] none initial work).flatMap
              (SourceTask.positions true)).Nodup)
    (run : AdmissibleRun work ⟨groups, streams, batches.flatten⟩)
    (zero : (replayResponse response groups streams batches).totalErrors = 0)
    (containers : Bool)
    : ∃ produced final,
        decodeAtoms containers initial
            (batches.flatten.flatten.flatMap eventPositionAtoms)
          = some (produced, final)
        ∧ produced.Perm
            ((sourceTasks [] none initial work).flatMap
              (SourceTask.positions containers)) := by
  obtain ⟨events, matching, explained, _, batched, covered⟩ :=
    replayResponse_successful_history positive run zero
  have exactDecode := decode_historyPositionAtoms (containers := containers)
    explained seeded initialHistory disjoint events.length (Nat.le_refl _)
  have nodePaths : ∀ node ∈ (events ++ [WorkEvent.workQueueTermination]).flatMap
      eventNodes, paths node.key = node.path := by
    intro node member
    simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, eventNodes,
      List.append_nil] at member
    obtain ⟨kind, parents, birth, known⟩ := explained_nodes explained node member
    exact (workAt_node coherent known).2
  have atoms := workBatching_positionAtoms batched nodePaths
  refine ⟨_, sourceHistoryCursors (sourceTasks [] none initial work) matching events
    initial events.length, ?_, (sourcePrefixTasks_perm explained
    (fun occurrence owners producer payload known =>
      (covered occurrence owners producer payload known).1)).flatMap_right
        (SourceTask.positions containers)⟩
  rw [atoms]
  simpa [eventPositionAtoms] using exactDecode

end GraphQL.IncrementalDelivery.Correctness
