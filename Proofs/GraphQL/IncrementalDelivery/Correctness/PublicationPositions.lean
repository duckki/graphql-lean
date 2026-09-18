import Proofs.GraphQL.IncrementalDelivery.Correctness.HistoryStreamCursors
import Proofs.GraphQL.IncrementalDelivery.Correctness.WorkPositionAtoms

/-! Supplied value publications select distinct members of the disjoint source inventory. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open WorkScheduler

/-- The source label for a supplied value publication; controls carry no source label. -/
def sourceEventTask (tasks : List SourceTask) (matching : PublicationMatching)
    (index : Nat) (event : WorkEvent)
    : Option SourceTask :=
  match event with
  | .groupValues .. | .streamValues .. =>
      tasks.find? (fun task => decide (task.occurrence = matching index))
  | _ => none

/-- A selected source label is an inventory member matched to a value output. -/
theorem sourceEventTask_some {tasks matching index event task}
    (found : sourceEventTask tasks matching index event = some task)
    : task ∈ tasks ∧ task.occurrence = matching index ∧ IsValue event := by
  cases event <;> try contradiction
  all_goals
    exact ⟨List.mem_of_find?_eq_some found, by simpa using List.find?_some found, trivial⟩

/-- Every actual value output finds its unique source label; controls find none. -/
theorem sourceEventTask_value {initial work matching index event task}
    (value : IsValue event) (member : task ∈ sourceTasks [] none initial work)
    (same : task.occurrence = matching index)
    : sourceEventTask (sourceTasks [] none initial work) matching index event
      = some task := by
  cases event <;> try contradiction
  all_goals simpa only [sourceEventTask, ← same] using sourceTasks_find member

/-- The source labels published in the first cut supplied outputs, in observation order.
-/
def sourcePrefixTasks (tasks : List SourceTask) (matching : PublicationMatching)
    (events : List WorkEvent)
    : Nat → List SourceTask
  | 0 => []
  | cut + 1 =>
      sourcePrefixTasks tasks matching events cut
      ++ ((events[cut]?).bind (sourceEventTask tasks matching cut)).toList

/-- Every prefix label has an actual earlier matched publication and belongs to the
source inventory. Witness: induction on the finite observed prefix.
-/
theorem sourcePrefixTasks_member {tasks matching events cut task}
    (member : task ∈ sourcePrefixTasks tasks matching events cut)
    : task ∈ tasks
      ∧ ∃ index event,
          index < cut
          ∧ events[index]? = some event
          ∧ IsValue event
          ∧ matching index = task.occurrence := by
  induction cut with
  | zero => simp [sourcePrefixTasks] at member
  | succ cut ih =>
      rcases List.mem_append.mp member with prior | last
      · obtain ⟨belongs, index, event, earlier, selected, value, same⟩ := ih prior
        exact ⟨belongs, index, event, by omega, selected, value, same⟩
      · cases selected : events[cut]? with
        | none => simp [selected] at last
        | some event =>
            have found : sourceEventTask tasks matching cut event = some task := by
              simpa [selected] using last
            obtain ⟨belongs, same, value⟩ := sourceEventTask_some found
            exact ⟨belongs, cut, event, by omega, selected, value, same.symm⟩

/-- Prefix publications have pairwise-distinct source occurrences, for every matching
that explains the history. Witness: a repeated label would repeat a publication index.
-/
theorem sourcePrefixTasks_unique {work groups streams events matching failures}
    (explained : Explains work groups streams events matching failures)
    (tasks : List SourceTask) (cut : Nat)
    : (sourcePrefixTasks tasks matching events cut).Pairwise
        (fun first second => first.occurrence ≠ second.occurrence) := by
  induction cut with
  | zero => exact .nil
  | succ cut ih =>
      rw [sourcePrefixTasks, List.pairwise_append]
      refine ⟨ih, ?_, ?_⟩
      · cases (events[cut]?).bind (sourceEventTask tasks matching cut) <;> simp
      · intro first firstMember second secondMember equal
        obtain ⟨_, earlier, prior, before, atEarlier, priorValue, firstMatch⟩ :=
          sourcePrefixTasks_member firstMember
        cases selected : events[cut]? with
        | none => simp [selected] at secondMember
        | some event =>
            have found : sourceEventTask tasks matching cut event = some second := by
              simpa [selected] using secondMember
            obtain ⟨_, secondMatch, value⟩ := sourceEventTask_some found
            have impossible := explained.publication_unique atEarlier priorValue selected value
              (firstMatch.trans (equal.trans secondMatch))
            omega

/-- Selecting distinct source occurrences preserves global position uniqueness,
including separation from initial data. Witness: flattened source pairwise disjointness.
-/
theorem sourceSelection_positions_unique {inventory selected : List SourceTask}
    {initial : List ResponsePath}
    (source : (initial ++ inventory.flatMap (SourceTask.positions true)).Nodup)
    (members : selected.Subset inventory)
    (unique
      : selected.Pairwise (fun first second => first.occurrence ≠ second.occurrence))
    : (initial ++ selected.flatMap (SourceTask.positions true)).Nodup := by
  obtain ⟨initialUnique, sourceUnique, apart⟩ := List.nodup_append.mp source
  have each := (List.pairwise_flatMap.mp sourceUnique).1
  refine List.nodup_append.mpr ⟨initialUnique, ?_, ?_⟩
  · apply List.pairwise_flatMap.mpr
    refine ⟨fun task member => each task (members member), ?_⟩
    apply unique.imp_of_mem
    intro left right leftMember rightMember different first inFirst second inSecond equal
    subst second
    exact sourceTask_positions_disjoint sourceUnique (members leftMember)
      (members rightMember) different inFirst inSecond
  · intro first inInitial second inLater equal
    obtain ⟨task, member, position⟩ := List.mem_flatMap.mp inLater
    exact apart first inInitial second
      (List.mem_flatMap.mpr ⟨task, members member, position⟩) equal

/-- Every admitted prefix publishes disjoint source positions in its actual output order.
Witness: selected-label provenance, one-shot publication, and source position ownership.
-/
theorem sourcePrefix_positions_unique
    {work groups streams events matching failures initial positions}
    (explained : Explains work groups streams events matching failures)
    (source
      : (positions
          ++ (sourceTasks [] none initial work).flatMap
              (SourceTask.positions true)).Nodup) (cut : Nat)
    : (positions
        ++ List.flatMap (SourceTask.positions true)
            (sourcePrefixTasks (sourceTasks [] none initial work) matching events
              cut)).Nodup :=
  sourceSelection_positions_unique source
    (fun _ member => (sourcePrefixTasks_member member).1)
    (sourcePrefixTasks_unique explained _ cut)

end GraphQL.IncrementalDelivery.Correctness
