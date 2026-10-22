import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.LiteralDeferredPlans
import Tests.GraphQL.IncrementalDelivery.Execution

/-! A plan built by the original actual collector contains an early stream, a failed
defer group, a later stream and a nested defer/ancestor pair. Constructed literal leaves
give one final witness; an initial-fatal variant checks that no deferred task executes. -/

namespace AlternativeLiteralPlanChecks

open GraphQL.IncrementalDelivery
open Execution AlternativeWorkQueue.NativeRefinement
open GraphQL.IncrementalDelivery.Semantics
open KeyRenaming ScheduledErrors ScheduledWork

private def selections : List Selection :=
  [
    Tests.field "values" [] [.stream] (some "early"),
    Tests.defer
      [
        Tests.field "fail" [] [] (some "nullable"),
        Tests.field "required" [] [] (some "first"),
        Tests.field "required" [] [] (some "second"),
        Tests.field "values" [] [.stream] (some "skipped")
      ],
    Tests.defer [Tests.field "values" [] [.stream] (some "later")],
    Tests.defer [Tests.defer [Tests.field "values" [] [.stream] (some "nested")]]
  ]

private def collected :=
  (collectFields Tests.schema [] "Query"
    (.object "Query" 0 : ResolverValue Nat) selections).run
    0

private def actualPlan := buildExecutionPlan collected.1.collectedFieldsMap []

private def details (name : GraphQL.Name) (deferUsage : Option DeferUsage := none)
    : FieldDetails :=
  {
    fieldName := name,
    arguments := [],
    selectionSet := [],
    directives := if name == "values" then [.stream] else [],
    deferUsage := deferUsage
  }

private def expectedPlan : ExecutionPlan :=
  {
    collectedFieldsMap := [("early", [details "values"])],
    newCollectedFieldsMaps :=
      [
        (
          [0],
          [
            ("nullable", [details "fail" (some { ref := 0 })]),
            ("first", [details "required" (some { ref := 0 })]),
            ("second", [details "required" (some { ref := 0 })]),
            ("skipped", [details "values" (some { ref := 0 })])
          ]
        ),
        ([1], [("later", [details "values" (some { ref := 1 })])]),
        ([3], [("nested", [details "values" (some { ref := 3, ancestors := [2] })])])
      ]
  }

private theorem actual_plan : actualPlan = expectedPlan := by cbv
example : collected.2 = 4 := by cbv

private theorem details_literal (name : GraphQL.Name) (usage : Option DeferUsage)
    (allowed : name = "fail" ∨ name = "required" ∨ name = "values")
    : LiteralFieldValues Tests.resolvers "Query" (.object "Query" 0)
        [details name usage] := by
  intro field member arguments value resolved
  simp only [List.mem_singleton] at member
  subst field
  rcases allowed with rfl | rfl | rfl
  · change none = some value at resolved
    cases resolved
  · change none = some value at resolved
    cases resolved
  · change some (.list [.scalar "x", .null, .scalar "z"]) = some value at resolved
    cases resolved
    apply LiteralValue.list
    intro value member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    obtain rfl | rfl | rfl := member
    · exact .scalar _
    · exact .null
    · exact .scalar _

private theorem initial_literal
    : LiteralFields Tests.resolvers "Query" (.object "Query" 0)
        actualPlan.collectedFieldsMap := by
  rw [actual_plan]
  intro entry member
  simp only [expectedPlan, List.mem_singleton] at member
  subst entry
  exact details_literal _ _ (.inr (.inr rfl))

private theorem deferred_literal
    : LiteralPartitions Tests.resolvers "Query" (.object "Query" 0)
        actualPlan.newCollectedFieldsMaps := by
  rw [actual_plan]
  intro partition member entry inFields
  simp only [expectedPlan, List.mem_cons, List.not_mem_nil, or_false] at member
  obtain rfl | rfl | rfl := member
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at inFields
    obtain rfl | rfl | rfl | rfl := inFields
    · exact details_literal _ _ (.inl rfl)
    · exact details_literal _ _ (.inr (.inl rfl))
    · exact details_literal _ _ (.inr (.inl rfl))
    · exact details_literal _ _ (.inr (.inr rfl))
  · simp only [List.mem_singleton] at inFields
    subst entry
    exact details_literal _ _ (.inr (.inr rfl))
  · simp only [List.mem_singleton] at inFields
    subst entry
    exact details_literal _ _ (.inr (.inr rfl))

private theorem initial_bound : FieldsBelow 4 actualPlan.collectedFieldsMap := by
  rw [actual_plan]
  intro entry member field inFields key inKeys
  simp only [expectedPlan, List.mem_singleton] at member
  subst entry
  simp only [List.mem_singleton] at inFields
  subst field
  simp [fieldKeys, details] at inKeys

private theorem deferred_bound : PartitionsBelow 4 actualPlan.newCollectedFieldsMaps := by
  rw [actual_plan]
  intro partition member
  simp only [expectedPlan, List.mem_cons, List.not_mem_nil, or_false] at member
  obtain rfl | rfl | rfl := member
  all_goals constructor
  all_goals first
    | (intro key member; simp only [List.mem_singleton] at member; subst key; omega)
    | (intro entry member field inFields key inKeys
       simp only [List.mem_cons, List.not_mem_nil, or_false] at member
       rcases member with rfl | rfl | rfl | rfl
       all_goals simp only [List.mem_singleton] at inFields
       all_goals subst field
       all_goals simp [fieldKeys, details] at inKeys
       all_goals omega)

private def cut :=
  (ScheduledExecution.executeExecutionPlan Tests.schema Tests.resolvers [] 7
    "Query" (.object "Query" 0) collected.1.newDeferUsages actualPlan [] [] []).run
    4

private def eager :=
  (Execution.executeExecutionPlan Tests.schema Tests.resolvers [] 7 "Query"
    (.object "Query" 0) (collected.1.newDeferUsages.map (usage id)) (plan id actualPlan)
    [] (([] : List Nat).map id) (([] : DeferMap).map (fragment id))).run
    4

private theorem constructed : ∃ next, RunRefines id next 4 4 cut eager := by
  exact literalExecutionPlanRefinement_holds _ Tests.schema Tests.resolvers [] 7 "Query"
    (.object "Query" 0)
    collected.1.newDeferUsages actualPlan [] [] [] id 4 4
    initial_literal deferred_literal
    ⟨fun _ _ same => same, fun _ earlier => earlier, rfl, fun _ => rfl⟩
    initial_bound deferred_bound
    (by simp)
    (by
      have boundedKeys : (getNewDeferMap collected.1.newDeferUsages [] []).flatMap
          RefRoles.fragmentRefs = [0, 1, 2, 3, 2] := by cbv
      intro key member
      rw [boundedKeys] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      omega)

example : cut.2 = 7 ∧ eager.2 = 8 := by cbv

private theorem stream_key {keys : Nat → Nat} {before after : DeliveryNode}
    {items eagerItems}
    (known : WorkRefines keys (.stream before items) (.stream after eagerItems))
    : keys before.ref = after.ref := by cases known; rfl

example
    : ∃ next,
        next 0 = 0
        ∧ next 1 = 1
        ∧ next 2 = 2
        ∧ next 3 = 3
        ∧ next 4 = 4
        ∧ next 5 = 6
        ∧ next 6 = 7
        ∧ next 7 = 8
        ∧ CompletionRefines next cut.1 eager.1 := by
  obtain ⟨next, related⟩ := constructed
  have early := related.completion.2.1.locate [0, 0, 1]
  have later := related.completion.2.1.locate [1, 1, 0, 0, 0, 1]
  have nested := related.completion.2.1.locate [1, 1, 1, 0, 0, 0, 1]
  cbv at early later nested
  refine ⟨
    next,
    related.compatible 0 (by omega),
    related.compatible 1 (by omega),
    related.compatible 2 (by omega),
    related.compatible 3 (by omega),
    ?_,
    ?_,
    ?_,
    ?_,
    related.completion
  ⟩
  · exact stream_key early.1
  · exact stream_key later.1
  · exact stream_key nested.1
  · simpa only [show cut.2 = 7 by cbv, show eager.2 = 8 by cbv] using related.supplies.boundary

-- The failed group is retained, not caught as a nullable initial response or removed.
example
    : WorkQueueSemantics.locateWork cut.1.work [1, 0]
      = some
          ⟨
            .executionGroup [{ node := { ref := 0, path := [] } }] []
              { result := .error 2, cause := some 1 } .empty,
            none,
            []
          ⟩ := by cbv

example
    : WorkQueueSemantics.locateWork eager.1.work [1, 0]
      = some
          ⟨
            .executionGroup [{ node := { ref := 0, path := [] } }] []
              { result := .error 3, cause := some 1 } .empty,
            none,
            []
          ⟩ := by cbv

-- The construction is consumed by the actual original collection/root driver, not only
-- by a synthetic list of independently paired actions.
private theorem root_constructed
    : ∃ next,
        RunRefines id next 0 0
          ((ScheduledExecution.executeRootSelectionSetCore Tests.schema Tests.resolvers []
              7 "Query" (.object "Query" 0) selections).run
            0)
          ((Execution.executeRootSelectionSetCore Tests.schema Tests.resolvers [] 7
              "Query" (.object "Query" 0) selections).run
            0) := by
  have cutRoot : (ScheduledExecution.executeRootSelectionSetCore Tests.schema Tests.resolvers [] 7
      "Query" (.object "Query" 0) selections).run 0 = cut := by cbv
  have eagerRoot : (Execution.executeRootSelectionSetCore Tests.schema Tests.resolvers [] 7
      "Query" (.object "Query" 0) selections).run 0 = eager := by cbv
  rw [cutRoot, eagerRoot]
  obtain ⟨next, related⟩ := constructed
  exact ⟨next, ⟨fun _ earlier => False.elim (Nat.not_lt_zero _ earlier), related.supplies,
    Nat.zero_le _, Nat.zero_le _, related.bounded, related.completion⟩⟩

private def fatalInitial : ExecutionPlan :=
  {
    actualPlan with
      collectedFieldsMap :=
        [
          ("first", [details "required"]),
          ("second", [details "required"]),
          ("skipped", [details "values"])
        ]
  }

private def fatalCut :=
  (ScheduledExecution.executeExecutionPlan Tests.schema Tests.resolvers [] 7
    "Query" (.object "Query" 0) collected.1.newDeferUsages fatalInitial [] [] []).run
    4

private def fatalEager :=
  (Execution.executeExecutionPlan Tests.schema Tests.resolvers [] 7 "Query"
    (.object "Query" 0) (collected.1.newDeferUsages.map (usage id)) (plan id fatalInitial)
    [] (([] : List Nat).map id) (([] : DeferMap).map (fragment id))).run
    4

private theorem fatal_constructed
    : ∃ next, RunRefines id next 4 4 fatalCut fatalEager := by
  apply literalExecutionPlanRefinement_holds _ Tests.schema Tests.resolvers [] 7 "Query"
    (.object "Query" 0) collected.1.newDeferUsages fatalInitial [] [] [] id 4 4
  · intro entry member
    simp only [fatalInitial, List.mem_cons, List.not_mem_nil, or_false] at member
    obtain rfl | rfl | rfl := member
    · exact details_literal _ _ (.inr (.inl rfl))
    · exact details_literal _ _ (.inr (.inl rfl))
    · exact details_literal _ _ (.inr (.inr rfl))
  · exact deferred_literal
  · exact ⟨fun _ _ same => same, fun _ earlier => earlier, rfl, fun _ => rfl⟩
  · intro entry member field inFields key inKeys
    simp only [fatalInitial, List.mem_cons, List.not_mem_nil, or_false] at member
    obtain rfl | rfl | rfl := member
    all_goals simp only [List.mem_singleton] at inFields
    all_goals subst field
    all_goals simp [fieldKeys, details] at inKeys
  · exact deferred_bound
  · simp
  · have boundedKeys : (getNewDeferMap collected.1.newDeferUsages [] []).flatMap
        RefRoles.fragmentRefs = [0, 1, 2, 3, 2] := by cbv
    intro key member
    rw [boundedKeys] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    omega

-- Neither run constructs deferred groups after the initial fatal outcome.
example
    : fatalCut.1 = .error 1
      ∧ fatalEager.1 = {Completion.error 2 with cause := some 1} := by cbv

example : fatalCut.2 = 4 ∧ fatalEager.2 = 5 := by cbv

example : LiteralDeferredGroupRefinement := literalDeferredGroupRefinement_holds
example : LiteralExecutionPlanRefinement := literalExecutionPlanRefinement_holds

#print axioms literalDeferredGroupRefinement_holds
#print axioms literalExecutionPlanRefinement_holds
#print axioms constructed
#print axioms root_constructed
#print axioms fatal_constructed

end AlternativeLiteralPlanChecks
