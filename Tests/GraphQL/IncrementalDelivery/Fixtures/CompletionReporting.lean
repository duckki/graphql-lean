import Tests.GraphQL.IncrementalDelivery.Execution
import Proofs.GraphQL.IncrementalDelivery.Semantics.CompletionReporting

/-! Delivery-boundary projections and supported task-cause selection. The pure
executor collects both sibling errors; these examples do not model early cancellation.
-/

namespace GraphQL.IncrementalDelivery.Tests.CompletionReporting

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics.CompletionReporting

private def schema : Schema :=
  {
    queryType := "Query"
    types :=
      [
        .object
          {
            name := "Query",
            fields :=
              [
                { name := "x", outputType := .named "String" },
                { name := "bad", outputType := .nonNull (.named "String") },
                { name := "child", outputType := .named "Child" },
                { name := "requiredChild", outputType := .nonNull (.named "Child") }
              ]
          },
        .object
          {
            name := "Child",
            fields :=
              [
                { name := "x", outputType := .named "String" },
                { name := "bad", outputType := .nonNull (.named "String") }
              ]
          }
      ]
  }

private def resolvers : Resolvers Nat :=
  {
    resolve :=
      fun _ field _ _ =>
        match field with
        | "x" | "bad" => none
        | _ => some (.object "Child" 1)
    resolve_argumentsEquivalent := by intros; rfl
  }

private def fields : List Selection := [field "x", field "bad"]

private def group (selections : List Selection)
    : Completion (List (Name × ResponseValue)) :=
  let (collected, supply) :=
    (collectFields schema [] "Query" (.object "Query" 0) selections).run 0
  (executeExecutionGroup schema resolvers [] 10 "Query" (.object "Query" 0)
    collected.collectedFieldsMap [] [] []).run
    supply
  |>.1

private def query (selections : List Selection) : ExecutionResult :=
  executeRootSelectionSet unavailable schema resolvers [] 10 "Query" (.object "Query" 0)
    selections

-- Both errors have been collected before the failed payload is projected.
#guard same (group fields).result (.error 2 : Result (List (Name × ResponseValue)))
#guard (group fields).cause == some 1
#guard
  same (group fields).deliveryResult (.error 1 : Result (List (Name × ResponseValue)))

-- Ordinary response projection preserves both errors, including the basic executor.
#guard
  match query fields with
  | .single response => same response { data := .null, errors := 2 : Response }
  | _ => false

#guard
  same
    (selectionSetResultToResponse
      (GraphQL.Execution.executeRootSelectionSet schema resolvers [] 10 "Query"
        (.object "Query" 0) (SelectionSet.eraseIncrementalDirectives fields)))
    { data := .null, errors := 2 : Response }

-- A nullable error accompanying delivered data remains in the successful payload.
#guard
  same (group [field "x"]).deliveryResult
    (.ok ([("x", .null)], 1) : Result (List (Name × ResponseValue)))

-- A caught child failure explains delivered null data, retaining both diagnostics.
#guard
  same (group [field "child" fields]).deliveryResult
    (.ok ([("child", .null)], 2) : Result (List (Name × ResponseValue)))

-- If that null escapes an enclosing non-null wrapper, its original cause is rethrown.
#guard
  same (group [field "requiredChild" fields]).result
    (.error 2 : Result (List (Name × ResponseValue)))
#guard
  same (group [field "requiredChild" fields]).deliveryResult
    (.error 1 : Result (List (Name × ResponseValue)))

private def item (itemType : TypeRef) : Completion ResponseValue :=
  (completeValue schema resolvers [] 10 itemType
    [{ fieldName := "items", arguments := [], selectionSet := fields }]
    (.object "Child" 1) [.field "items", .index 0] [] [] false).run
    0
  |>.1

-- Streamed non-null objects use the item boundary; nullable items deliver null instead.
#guard same (item (.nonNull (.named "Child"))).result (.error 2 : Result ResponseValue)
#guard
  same (item (.nonNull (.named "Child"))).deliveryResult (.error 1 : Result ResponseValue)
#guard same (item (.named "Child")).deliveryResult (.ok (.null, 2) : Result ResponseValue)

-- A list caught inside a delivered payload preserves diagnostics from every item.
private def list : Completion ResponseValue :=
  (completeValue schema resolvers [] 10 (.list (.nonNull (.named "Child")))
    [{ fieldName := "items", arguments := [], selectionSet := fields }]
    (.list [.object "Child" 1, .object "Child" 2]) [] [] [] false).run
    0
  |>.1

#guard same list.deliveryResult (.ok (.null, 4) : Result ResponseValue)
#guard same list.nonNull.deliveryResult (.error 1 : Result ResponseValue)

-- Initial nullable diagnostics remain in the initial incremental envelope.
#guard
  match query [field "x", defer [field "child" [field "x"]]] with
  | .incremental initial _ =>
      initial.errors == 1 && same initial.data (.object [("x", .null)])
  | _ => false

-- A root bubble cancels unexposed work and preserves the initial two-error response.
#guard
  match query (fields ++ [defer [field "x"]]) with
  | .single response => same response { data := .null, errors := 2 : Response }
  | _ => false

-- Explanation selection preserves the selected count; it does not replace all errors by 1.
private def left : Completion ResponseValue :=
  Completion.combine (fun _ _ => ResponseValue.null)
    ({ result := .ok (.null, 7) } : Completion ResponseValue)
    (Completion.error 3 : Completion ResponseValue)

private def both : Completion ResponseValue :=
  Completion.combine (fun _ _ => ResponseValue.null) left
    (Completion.error 5 : Completion Unit)

#guard same both.result (.error 15 : Result ResponseValue)
#guard same both.deliveryResult (.error 3 : Result ResponseValue)
#guard same ((both.catchNull id).nonNull).deliveryResult (.error 3 : Result ResponseValue)

example : CauseValid both := by
  apply combine_valid
  · apply combine_valid
    · simp [CauseValid]
    · exact error_valid 3 (by decide)
  · exact error_valid 5 (by decide)

-- Raw syntax does not gain an invented cause if its optional metadata is absent.
#guard
  same ({ result := .error 0 } : Completion Unit).deliveryResult (.error 0 : Result Unit)

-- Group-level selection must be supported by an accepted contributing failure.
open GraphQL.IncrementalDelivery.WorkQueueSemantics

private def node : DeliveryNode := { ref := 0, path := [] }

private def work : Work :=
  .combine (.executionGroup [⟨node, []⟩] [] { result := .error 3 } .empty)
    (.executionGroup [⟨node, []⟩] [] { result := .error 5 } .empty)

private def failures : List Occurrence := [.executionGroup [0], .executionGroup [1]]

example : NodeFailureCause work failures 0 3 := by
  refine ⟨
    .executionGroup [0],
    by simp [failures],
    [0],
    none,
    .object [] (.error 3),
    ?_,
    by simp,
    rfl,
    by decide
  ⟩
  exact ⟨[⟨node, []⟩], [], { result := .error 3 }, .empty, [], rfl, rfl, rfl⟩

example : NodeFailureCause work failures 0 5 := by
  refine ⟨
    .executionGroup [1],
    by simp [failures],
    [0],
    none,
    .object [] (.error 5),
    ?_,
    by simp,
    rfl,
    by decide
  ⟩
  exact ⟨[⟨node, []⟩], [], { result := .error 5 }, .empty, [], rfl, rfl, rfl⟩

-- Neither their sum nor an unrelated positive count is an explanation from these tasks.
example (errors : Nat) (other : errors ≠ 3 ∧ errors ≠ 5)
    : ¬NodeFailureCause work failures 0 errors := by
  rintro ⟨occurrence, member, owners, producer, payload, known, _, failed, _⟩
  simp only [failures, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;>
    simp [TaskAt, Located, locateWork, locateWork.go, WorkLocation.child?, work] at known <;>
    rcases known with ⟨groups, path, result, ⟨⟨hg, hp, hr⟩, _⟩, ho, hv⟩ <;>
    subst groups path result owners payload <;>
    simp_all [Payload.failure, TaskOutcome.deliveryResult]

example : ¬NodeFailureCause work [] 0 3 := by
  simp [NodeFailureCause]

example : ¬NodeFailureCause work failures 1 3 := by
  rintro ⟨occurrence, member, owners, producer, payload, known, owner, _⟩
  simp only [failures, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;>
    simp [TaskAt, Located, locateWork, locateWork.go, WorkLocation.child?, work, node] at known <;>
    rcases known with ⟨groups, path, result, ⟨⟨hg, hp, hr⟩, _⟩, ho, hv⟩ <;>
    subst groups path result owners payload <;>
    simp_all

end GraphQL.IncrementalDelivery.Tests.CompletionReporting
