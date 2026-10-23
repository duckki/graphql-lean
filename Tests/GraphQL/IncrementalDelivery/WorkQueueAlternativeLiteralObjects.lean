import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.LiteralObjectRefinement
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Actual object collection/completion after an existing gap, with inherited ancestry,
a failed deferred group and later nested metadata/streams. The theorem derives collection
and plan bounds; callers only establish the input domain and inherited metadata laws. -/

namespace AlternativeLiteralObjectChecks

open GraphQL.IncrementalDelivery
open Execution AlternativeWorkQueue.NativeRefinement
open GraphQL.IncrementalDelivery.Semantics
open KeyRenaming ScheduledErrors ScheduledWork

private def selections : List Selection :=
  [
    Tests.field "values" [] [.stream] (some "early"),
    Tests.defer
      [
        Tests.field "required" [] [] (some "first"),
        Tests.field "required" [] [] (some "second"),
        Tests.field "values" [] [.stream] (some "skipped")
      ],
    Tests.defer [Tests.field "values" [] [.stream] (some "later")],
    Tests.defer [Tests.defer [Tests.field "values" [] [.stream] (some "nested")]]
  ]

private def fields : List FieldDetails :=
  [{
    fieldName := "user",
    arguments := [],
    selectionSet := selections,
    deferUsage := some { ref := 17, ancestors := [16] }
  }]

private def context : DeferMap :=
  [
    { node := { ref := 16, path := [] } },
    { node := { ref := 17, path := [] }, ancestors := [{ ref := 16, path := [] }] }
  ]

private def keys : Nat → Nat := retargetTail id 18 21

private theorem initial : SupplyMap keys 20 23 := by
  have prefixBound : PrefixBelow id 18 21 := by intro key earlier; dsimp; omega
  refine ⟨
    retargetTail_injective (fun _ _ same => same) prefixBound,
    ?_,
    ?_,
    (retargetTail_fresh id 18 21).advance (by omega)
  ⟩
  · intro key earlier
    unfold keys retargetTail
    split
    · change key < 23
      omega
    · omega
  · cbv

private def collected :=
  (collectSubfields Tests.schema [] "User"
    (.object "User" 1 : ResolverValue Nat) fields).run
    20

private def details (name : GraphQL.Name) (usage : DeferUsage) : FieldDetails :=
  {
    fieldName := name,
    arguments := [],
    selectionSet := [],
    directives := if name == "values" then [.stream] else [],
    deferUsage := some usage
  }

private def expectedFields : CollectedFieldsMap :=
  [
    ("early", [details "values" { ref := 17, ancestors := [16] }]),
    ("first", [details "required" { ref := 20, ancestors := [17, 16] }]),
    ("second", [details "required" { ref := 20, ancestors := [17, 16] }]),
    ("skipped", [details "values" { ref := 20, ancestors := [17, 16] }]),
    ("later", [details "values" { ref := 21, ancestors := [17, 16] }]),
    ("nested", [details "values" { ref := 23, ancestors := [22, 17, 16] }])
  ]

private theorem collected_fields : collected.1.collectedFieldsMap = expectedFields := by
  cbv

private theorem details_literal (name : GraphQL.Name) (usage : DeferUsage)
    (allowed : name = "required" ∨ name = "values")
    : LiteralFieldValues Tests.resolvers "User" (.object "User" 1)
        [details name usage] := by
  intro field member arguments value resolved
  simp only [List.mem_singleton] at member
  subst field
  rcases allowed with rfl | rfl
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

private theorem literal
    : LiteralFields Tests.resolvers "User" (.object "User" 1)
        collected.1.collectedFieldsMap := by
  rw [collected_fields]
  intro entry member
  simp only [expectedFields, List.mem_cons, List.not_mem_nil, or_false] at member
  obtain rfl | rfl | rfl | rfl | rfl | rfl := member
  · exact details_literal _ _ (.inr rfl)
  · exact details_literal _ _ (.inl rfl)
  · exact details_literal _ _ (.inl rfl)
  · exact details_literal _ _ (.inr rfl)
  · exact details_literal _ _ (.inr rfl)
  · exact details_literal _ _ (.inr rfl)

private def path : ResponsePath := [.field "user"]

private def cut :=
  (ScheduledExecution.completeValue Tests.schema Tests.resolvers [] 8
    (.named "User") fields (.object "User" 1) path [17] context true).run
    20

private def eager :=
  (Execution.completeValue Tests.schema Tests.resolvers [] 8
    (.named "User") (fields.map (field keys)) (.object "User" 1) path ([17].map keys)
    (context.map (fragment keys)) true).run
    23

private theorem constructed : ∃ next, RunRefines keys next 20 23 cut eager := by
  apply literalObjectCompletionRefinement_holds _ Tests.schema Tests.resolvers [] 7
    "User" "User" 1 fields path [17] context true keys 20 23 initial
  · intro field member usage inUsage
    simp only [fields, List.mem_singleton] at member
    subst field
    simp only [Option.mem_def, Option.some.injEq] at inUsage
    subst usage
    refine ⟨by decide, ?_⟩
    intro ancestor member
    simp only [List.mem_singleton] at member
    subst ancestor
    decide
  · simp
  · intro key member
    simp [context, RefRoles.fragmentRefs] at member
    omega
  · exact literal

example : collected.2 = 24 := by cbv
example : cut.2 = 27 ∧ eager.2 = 31 := by cbv

private theorem stream_key {keys : Nat → Nat} {before after : DeliveryNode}
    {items eagerItems}
    (known : WorkRefines keys (.stream before items) (.stream after eagerItems))
    : keys before.ref = after.ref := by cases known; rfl

example
    : ∃ next,
        next 16 = 16
        ∧ next 17 = 17
        ∧ next 24 = 27
        ∧ next 25 = 29
        ∧ next 26 = 30
        ∧ next 27 = 31
        ∧ CompletionRefines next cut.1 eager.1 := by
  obtain ⟨next, related⟩ := constructed
  have early := related.completion.2.1.locate [0, 0, 1]
  have later := related.completion.2.1.locate [1, 1, 0, 0, 0, 1]
  have nested := related.completion.2.1.locate [1, 1, 1, 0, 0, 0, 1]
  cbv at early later nested
  refine ⟨next, ?_, ?_, stream_key early.1, stream_key later.1, stream_key nested.1,
    ?_, related.completion⟩
  · exact (related.compatible 16 (by omega)).trans (by cbv)
  · exact (related.compatible 17 (by omega)).trans (by cbv)
  · simpa only [show cut.2 = 27 by cbv, show eager.2 = 31 by cbv] using related.supplies.boundary

-- Full owner and flattened-ancestor metadata is covered by the same Work relation.
example
    : WorkQueueSemantics.locateWork cut.1.work [1, 1, 1, 0]
      = some
          ⟨
            .executionGroup
              [{
                node := { ref := 23, path := path },
                ancestors :=
                  [
                    { ref := 22, path := path },
                    { ref := 17, path := [] },
                    { ref := 16, path := [] }
                  ]
              }]
              path ({ result := .ok ([("nested", .list [])], 0) })
              (.combine
                (.combine .empty
                  (.stream { ref := 26, path := path ++ [.field "nested"] }
                    [
                      ({ result := .ok (.scalar "x", 0) }, .empty),
                      ({ result := .ok (.null, 0) }, .empty),
                      ({ result := .ok (.scalar "z", 0) }, .empty)
                    ]))
                .empty),
            none,
            []
          ⟩ := by cbv

private def fatalFields : List FieldDetails :=
  [{
    fieldName := "user",
    arguments := [],
    selectionSet :=
      [
        Tests.field "required" [] [] (some "first"),
        Tests.field "required" [] [] (some "second"),
        Tests.field "values" [] [.stream] (some "skipped")
      ],
    deferUsage := some { ref := 17, ancestors := [16] }
  }]

private def fatalCut :=
  (ScheduledExecution.completeValue Tests.schema Tests.resolvers [] 8
    (.named "User") fatalFields (.object "User" 1) path [17] context true).run
    20

private def fatalEager :=
  (Execution.completeValue Tests.schema Tests.resolvers [] 8
    (.named "User") (fatalFields.map (field keys)) (.object "User" 1) path ([17].map keys)
    (context.map (fragment keys)) true).run
    23

private theorem fatal_constructed
    : ∃ next, RunRefines keys next 20 23 fatalCut fatalEager := by
  apply literalObjectCompletionRefinement_holds _ Tests.schema Tests.resolvers [] 7
    "User" "User" 1 fatalFields path [17] context true keys 20 23 initial
  · intro field member usage inUsage
    simp only [fatalFields, List.mem_singleton] at member
    subst field
    simp only [Option.mem_def, Option.some.injEq] at inUsage
    subst usage
    refine ⟨by decide, ?_⟩
    intro ancestor member
    simp only [List.mem_singleton] at member
    subst ancestor
    decide
  · simp
  · intro key member
    simp [context, RefRoles.fragmentRefs] at member
    omega
  · have collectedFatal : ((collectSubfields Tests.schema [] "User"
        (.object "User" 1) fatalFields).run 20).1.collectedFieldsMap
        = [("first", [details "required" { ref := 17, ancestors := [16] }]),
          ("second", [details "required" { ref := 17, ancestors := [16] }]),
          ("skipped", [details "values" { ref := 17, ancestors := [16] }])] := by cbv
    rw [collectedFatal]
    intro entry member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    obtain rfl | rfl | rfl := member
    · exact details_literal _ _ (.inl rfl)
    · exact details_literal _ _ (.inl rfl)
    · exact details_literal _ _ (.inr rfl)

-- Initial object failure is caught as nullable data, but the skipped fresh allocation
-- still changes the map used by a later enclosing sibling.
example : fatalCut.1.result = .ok (.null, 1) ∧ fatalEager.1.result = .ok (.null, 2) := by
  cbv

example : fatalCut.2 = 20 ∧ fatalEager.2 = 24 := by cbv

example
    : ∃ next,
        next 16 = 16
        ∧ next 17 = 17
        ∧ next 20 = 24
        ∧ CompletionRefines next fatalCut.1 fatalEager.1 := by
  obtain ⟨next, related⟩ := fatal_constructed
  refine ⟨next, ?_, ?_, ?_, related.completion⟩
  · exact (related.compatible 16 (by omega)).trans (by cbv)
  · exact (related.compatible 17 (by omega)).trans (by cbv)
  · simpa only [show fatalCut.2 = 20 by cbv, show fatalEager.2 = 24 by cbv]
      using related.supplies.boundary

example : LiteralObjectCompletionRefinement := literalObjectCompletionRefinement_holds

#print axioms literalObjectCompletionRefinement_holds
#print axioms build_plan_below
#print axioms constructed
#print axioms fatal_constructed

end AlternativeLiteralObjectChecks
