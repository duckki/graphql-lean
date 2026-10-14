import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.PreorderPlanning

/-! Explicit enter/exit traversal of the same finite forest. List heads are stack tops;
scan frames package sibling scheduling, while close frames retain the entered node's
ordinal. Empty scan frames are administrative, not native node visits. No subtree size
is consulted by a transition. Fuel only totalizes this proof-side observer.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.StackPlanning

open GraphQL.IncrementalDelivery.Execution
open PreorderPlanning

-----------------------------------------------------------------------------------------
-- Explicit frontier, counter and exit observations
-----------------------------------------------------------------------------------------

inductive Frame where
  | scan (forest : Forest) (parents : List Nat)
  | close (key : Nat) (parents : List Nat) (start : Nat)
deriving Repr

structure Result where
  ordinal : Nat
  completed : List Entry
  visits : Nat
  finished : Bool
deriving Repr

def run : Nat → Nat → List Frame → Result
  | _, ordinal, [] => ⟨ordinal, [], 0, true⟩
  | 0, ordinal, _ :: _ => ⟨ordinal, [], 0, false⟩
  | fuel + 1, ordinal, .scan .empty _ :: rest => run fuel ordinal rest
  | fuel + 1, ordinal, .scan (.node key children siblings) parents :: rest =>
      let tail :=
        run fuel (ordinal + 1)
          (.scan children (key :: parents)
            :: .close key parents ordinal
            :: .scan siblings parents
            :: rest)
      { tail with visits := tail.visits + 1 }
  | fuel + 1, ordinal, .close key parents start :: rest =>
      let tail := run fuel ordinal rest
      {
        tail with
          completed :=
            ⟨{ ref := key, ancestors := parents }, ⟨start, ordinal⟩⟩ :: tail.completed
          visits := tail.visits + 1
      }

/-- Sufficient exact administrative fuel, not a traversal counter or runtime bound. -/
def budget : Forest → Nat
  | .empty => 1
  | .node _ children siblings => 2 + budget children + budget siblings

/-- Structural observer of exit order only; run constructs its stops from the counter. -/
def exits (forest : Forest) (base : Nat) (parents : List Nat) : List Entry :=
  match forest with
  | .empty => []
  | .node key children siblings =>
      exits children (base + 1) (key :: parents)
      ++ (⟨{ ref := key, ancestors := parents }, ⟨base, base + 1 + children.keys.length⟩⟩
          :: exits siblings (base + 1 + children.keys.length) parents)

def traverse (forest : Forest) : Result := run (budget forest) 0 [.scan forest []]

def StackPreorderOptimization : Prop :=
  ∀ forest : Forest,
    let observed := traverse forest
    observed.finished = true
    ∧ observed.ordinal = forest.keys.length
    ∧ observed.visits = 2 * forest.keys.length
    ∧ observed.completed.Perm (forest.encode 0 [])

def StackPlanningOptimization : Prop :=
  ∀ forest : Forest,
    forest.keys.Nodup
    → ∀ groups parent,
        (∀ group ∈ groups, FieldsFromForest forest group.2)
        → let observed :=
            IntervalPlanning.buildPlan (makeIndex (traverse forest).completed) groups
              parent
          observed.project = buildExecutionPlan groups parent
          ∧ CanonicalPlanning.KeysMatch observed.partitions
          ∧ (observed.partitions.map CanonicalPlanning.KeyedPartition.key).Nodup

-----------------------------------------------------------------------------------------
-- Exact continuation theorem: a subtree closes before its sibling frontier resumes
-----------------------------------------------------------------------------------------

private theorem run_scan (forest : Forest) (base : Nat) (parents : List Nat)
    (fuel : Nat) (frames : List Frame)
    : run (fuel + budget forest) base (.scan forest parents :: frames)
      = let tail := run fuel (base + forest.keys.length) frames
        {
          tail with
            completed := exits forest base parents ++ tail.completed
            visits := tail.visits + 2 * forest.keys.length
        } := by
  induction forest generalizing base parents fuel frames with
  | empty => simp [budget, run, Forest.keys, exits]
  | node key children siblings childIH siblingIH =>
      have fuelEq : fuel + budget (.node key children siblings)
          = ((fuel + budget siblings + 1) + budget children) + 1 := by
        simp only [budget]; omega
      rw [fuelEq, run, childIH]
      simp only [run, siblingIH, exits, Forest.keys, List.length_cons, List.length_append]
      have counterEq : base + (children.keys.length + siblings.keys.length + 1)
          = base + 1 + children.keys.length + siblings.keys.length := by omega
      rw [counterEq]
      simp only [List.append_assoc, List.cons_append]
      congr 1
      omega

theorem budget_eq (forest : Forest) : budget forest = 3 * forest.keys.length + 1 := by
  induction forest with
  | empty => simp [budget, Forest.keys]
  | node key children siblings childIH siblingIH =>
      simp only [budget, Forest.keys, List.length_cons, List.length_append, childIH, siblingIH]
      omega

private theorem exits_perm (forest : Forest) (base : Nat) (parents : List Nat)
    : (exits forest base parents).Perm (forest.encode base parents) := by
  induction forest generalizing base parents with
  | empty => exact List.Perm.refl []
  | node key children siblings childIH siblingIH =>
      simp only [exits, Forest.encode]
      exact ((childIH _ _).append (List.Perm.cons _ (siblingIH _ _))).trans (List.perm_middle ..)

theorem StackPreorderOptimization_holds : StackPreorderOptimization := by
  intro forest
  have same := run_scan forest 0 [] 0 []
  simp only [Nat.zero_add, run, List.append_nil] at same
  simp only [traverse] at *
  rw [same]
  exact ⟨rfl, rfl, rfl, exits_perm forest 0 []⟩

theorem traverse_eq (forest : Forest)
    : traverse forest
      = ⟨forest.keys.length, exits forest 0 [], 2 * forest.keys.length, true⟩ := by
  simpa only [traverse, Nat.zero_add, run, List.append_nil]
    using run_scan forest 0 [] 0 []

-----------------------------------------------------------------------------------------
-- Exit order may differ, but the unique keyed index and plan do not
-----------------------------------------------------------------------------------------

theorem makeIndex_perm (left right : List Entry) (same : left.Perm right)
    (unique : (right.map (fun entry => entry.usage.ref)).Nodup)
    : makeIndex left = makeIndex right := by
  funext key
  have leftUnique := (same.symm.map (fun entry => entry.usage.ref)).nodup unique
  by_cases represented : ∃ entry ∈ right, entry.usage.ref = key
  · obtain ⟨entry, member, rfl⟩ := represented
    rw [makeIndex_entry right unique entry member,
      makeIndex_entry left leftUnique entry (same.mem_iff.mpr member)]
  · have rightAbsent : right.find? (fun entry => entry.usage.ref == key) = none := by
      simp only [List.find?_eq_none, beq_iff_eq]
      intro entry member equal
      exact represented ⟨entry, member, equal⟩
    have leftAbsent : left.find? (fun entry => entry.usage.ref == key) = none := by
      simp only [List.find?_eq_none, beq_iff_eq]
      intro entry member equal
      exact represented ⟨entry, same.mem_iff.mp member, equal⟩
    simp [makeIndex, rightAbsent, leftAbsent]

theorem traverse_index (forest : Forest) (unique : forest.keys.Nodup)
    : makeIndex (traverse forest).completed = makeIndex (forest.encode 0 []) := by
  apply makeIndex_perm _ _ (StackPreorderOptimization_holds forest).2.2.2
  simpa only [Forest.encode_keys] using unique

theorem StackPlanningOptimization_holds : StackPlanningOptimization := by
  intro forest unique groups parent fromForest
  rw [traverse_index forest unique]
  exact ForestPlanningOptimization_holds forest unique groups parent fromForest

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.StackPlanning
