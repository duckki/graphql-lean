import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.OrderedForestAssembly

/-! Ordered assembly is constructed from a parent table, not assumed from an endpoint. -/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OrderedForestAssembly.Tests

open GraphQL.IncrementalDelivery.Execution
open PreorderPlanning

example : OrderedForestConstruction := OrderedForestConstruction_holds
example : OrderedFieldPlanningOptimization := OrderedFieldPlanningOptimization_holds

private def contexts : Contexts := fun key => if key = 2 ∨ key = 1 then [0] else []
private def nodes : List Nat := [2, 0, 1, 4]

private theorem closed : ClosedContexts contexts nodes := by
  intro key member front ancestor suffix chain
  by_cases child : key = 2 ∨ key = 1
  · have eq : [0] = front ++ ancestor :: suffix := by simpa [contexts, child] using chain
    cases front with
    | nil =>
        simp only [List.nil_append, List.cons.injEq] at eq
        obtain ⟨rfl, rfl⟩ := eq
        simp [nodes, contexts]
    | cons first rest =>
        have length := congrArg List.length eq
        simp only [List.length_cons, List.length_nil, List.length_append] at length
        omega
  · simp [contexts, child] at chain

-- Native Map order is child-before-parent; assembly keeps sibling insertion order.
example : (assemble contexts nodes).keys = [0, 2, 1, 4] := rfl
example : forestRoots (assemble contexts nodes) = [0, 4] := rfl

example
    : childLists (assemble contexts nodes) = [(0, [2, 1]), (2, []), (1, []), (4, [])] :=
  rfl

example : (assemble contexts nodes).keys.Nodup :=
  (OrderedForestConstruction_holds contexts nodes (by decide) closed).1

private def detail (key : Nat) : FieldDetails :=
  {
    fieldName := "field",
    arguments := [],
    selectionSet := [],
    deferUsage := some { ref := key, ancestors := contexts key }
  }

private def groups : CollectedFieldsMap :=
  [("first", [detail 2]), ("next", [detail 1, detail 4])]

private theorem fields : FieldsInContexts contexts nodes groups := by
  intro group member usage present
  simp [groups] at member
  rcases member with rfl | rfl
  · simp [detail] at present
    subst usage
    simp [nodes]
  · simp [detail] at present
    rcases present with rfl | rfl <;> simp [nodes]

example : (discovered contexts nodes groups).nodes = [2, 0, 1, 4] := rfl
example : (fieldForest contexts nodes groups).keys = [0, 2, 1, 4] := rfl

example
    : (PlannerFieldMaps.buildMapPlan
        (makeIndex
          (PlannerNodeStack.traverse (fieldForest contexts nodes groups)).completed)
        groups []).project
      = buildExecutionPlan groups [] :=
  (OrderedFieldPlanningOptimization_holds contexts nodes groups [] closed fields
    (by decide)).2.2.1

-- A closed immediate-edge domain is insufficient if the stored full chain is inconsistent.
example : ¬ ClosedContexts (fun key => if key = 2 then [1, 0] else []) [2, 1, 0] := by
  intro bad
  have := (bad 2 (by simp) [] 1 [0] (by simp)).2
  simp at this

-- Neither a missing ancestor nor duplicate identities is licensed by the root contract.
example : ¬ ClosedContexts contexts [2] := by
  intro bad
  have := (bad 2 (by simp) [] 0 [] (by simp [contexts])).1
  simp at this

example : ¬ ([0, 0] : List Nat).Nodup := by decide
example : (assemble contexts []).keys = [] := rfl

#print axioms OrderedForestConstruction_holds
#print axioms OrderedFieldPlanningOptimization_holds

end
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OrderedForestAssembly.Tests
