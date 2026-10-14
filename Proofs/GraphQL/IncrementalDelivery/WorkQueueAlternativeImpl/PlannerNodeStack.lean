import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.PlannerFieldMaps

/-! Node-only frontier for the native enter/exit loop. Sibling/child scheduling uses
ordered bulk pushes, with exactly two loop visits per node and no administrative scans.
Enter/close tags observe the native node's unentered/entered state, not extra runtime nodes.
-/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.PlannerNodeStack

open GraphQL.IncrementalDelivery.Execution
open PreorderPlanning SerializedPlanning PlannerFieldMaps

-----------------------------------------------------------------------------------------
-- Ordered bulk pushes and node-only enter/exit transitions
-----------------------------------------------------------------------------------------

inductive Frame where
  | enter (key : Nat) (children : Forest) (parents : List Nat)
  | close (key : Nat) (parents : List Nat) (start : Nat)
deriving Repr

def pending (parents : List Nat) : Forest → List Frame
  | .empty => []
  | .node key children siblings => .enter key children parents :: pending parents siblings

abbrev Result := StackPlanning.Result

def run : Nat → Nat → List Frame → Result
  | _, ordinal, [] => ⟨ordinal, [], 0, true⟩
  | 0, ordinal, _ :: _ => ⟨ordinal, [], 0, false⟩
  | fuel + 1, ordinal, .enter key children parents :: rest =>
      let tail :=
        run fuel (ordinal + 1)
          (pending (key :: parents) children ++ .close key parents ordinal :: rest)
      { tail with visits := tail.visits + 1 }
  | fuel + 1, ordinal, .close key parents start :: rest =>
      let tail := run fuel ordinal rest
      {
        tail with
          completed :=
            ⟨{ ref := key, ancestors := parents }, ⟨start, ordinal⟩⟩ :: tail.completed
          visits := tail.visits + 1
      }

def traverse (forest : Forest) : Result :=
  run (2 * forest.keys.length) 0 (pending [] forest)

/-- Array contents from bottom to top; the logical frontier has its top at the head. -/
def pushReverse (stack nodes : List Frame) : List Frame := stack ++ nodes.reverse

def NodeStackOptimization : Prop :=
  ∀ forest : Forest, traverse forest = StackPlanning.traverse forest

def ReversePushOptimization : Prop :=
  ∀ stack nodes : List Frame, (pushReverse stack nodes).reverse = nodes ++ stack.reverse

def NodeStackMapPlanningOptimization : Prop :=
  ∀ forest : Forest,
    forest.keys.Nodup
    → ∀ groups parent,
        (groups.map Prod.fst).Nodup
        → (∀ group ∈ groups, FieldsFromForest forest group.2)
        → let index := makeIndex (traverse forest).completed
          let observed := buildMapPlan index groups parent
          observed.project = buildExecutionPlan groups parent
          ∧ Compatible index forest.keys observed.partitions
          ∧ (observed.partitions.map Partition.key).Nodup
          ∧ OrderedFields groups observed
          ∧ UniqueFieldMaps observed

-----------------------------------------------------------------------------------------
-- Child frontier closes before siblings; fuel counts actual node visits
-----------------------------------------------------------------------------------------

private theorem run_pending (forest : Forest) (base : Nat) (parents : List Nat)
    (fuel : Nat) (frames : List Frame)
    : run (fuel + 2 * forest.keys.length) base (pending parents forest ++ frames)
      = let tail := run fuel (base + forest.keys.length) frames
        {
          tail with
            completed := StackPlanning.exits forest base parents ++ tail.completed
            visits := tail.visits + 2 * forest.keys.length
        } := by
  induction forest generalizing base parents fuel frames with
  | empty => simp [pending, Forest.keys, StackPlanning.exits]
  | node key children siblings childIH siblingIH =>
      have fuelEq : fuel + 2 * (Forest.node key children siblings).keys.length
          = ((fuel + 2 * siblings.keys.length + 1) + 2 * children.keys.length) + 1 := by
        simp only [Forest.keys, List.length_cons, List.length_append]
        omega
      rw [fuelEq]
      simp only [pending, List.cons_append, run]
      rw [childIH]
      simp only [run, siblingIH, StackPlanning.exits, Forest.keys, List.length_cons, List.length_append]
      have counterEq : base + (children.keys.length + siblings.keys.length + 1)
          = base + 1 + children.keys.length + siblings.keys.length := by omega
      rw [counterEq]
      simp only [List.append_assoc, List.cons_append]
      congr 1
      omega

theorem NodeStackOptimization_holds : NodeStackOptimization := by
  intro forest
  have observed := run_pending forest 0 [] 0 []
  simp only [Nat.zero_add, run, List.append_nil] at observed
  rw [StackPlanning.traverse_eq]
  exact observed

theorem ReversePushOptimization_holds : ReversePushOptimization := by
  intro stack nodes
  simp [pushReverse]

theorem NodeStackMapPlanningOptimization_holds : NodeStackMapPlanningOptimization := by
  intro forest unique groups parent responseKeys fromForest
  rw [NodeStackOptimization_holds forest]
  exact StackMapPlanningOptimization_holds forest unique groups parent responseKeys fromForest

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.PlannerNodeStack
