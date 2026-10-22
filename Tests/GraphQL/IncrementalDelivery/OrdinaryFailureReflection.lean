import Proofs.GraphQL.IncrementalDelivery.Correctness.QueryFailureReflection
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Ordinary bubbling can come from deferred children of successful streamed items. -/

namespace GraphQL.IncrementalDelivery.Tests.OrdinaryFailureReflection
open GraphQL.IncrementalDelivery.Execution
open Correctness
open Correctness.OrdinaryFailures
open WorkQueueSemantics

private def schema : Schema :=
  {
    queryType := "Query",
    types :=
      [
        .object
          {
            name := "Query",
            fields :=
              [{
                name := "users", outputType := .nonNull (.list (.nonNull (.named "User")))
              }]
          },
        .object
          {
            name := "User",
            fields := [{ name := "required", outputType := .nonNull (.named "String") }]
          }
      ]
  }

private def selections : List Selection :=
  [field "users" [defer [field "required"]] [.stream (.boolean true) none (.int 0)]]

private def completed :=
  ((executeRootSelectionSetCore schema resolvers [] 30 "Query" (.object "Query" 0)
      selections).run
    0).1

/-- The initial response succeeds, while ordinary nested non-null bubbling reaches root.
Witness: actual root completion and ordinary execution reduction. Initial error counts
cannot detect these errors; the deferred failures must be retained for later reporting.
-/
example
    : completed.result = .ok ([("users", .list [])], 0)
      ∧ GraphQL.Execution.executeRootSelectionSet schema resolvers [] 30 "Query"
          (.object "Query" 0) (SelectionSet.eraseIncrementalDirectives selections)
        = .error 2 := by
  constructor <;> cbv

private def failedChild (node : DeliveryNode) : Work :=
  .combine .empty
    (.declareGroups [{ node }]
      (.combine
        (.executionGroup [{ node }] node.path
          { result := .error 1, cause := some 1 } .empty)
        .empty))

private theorem failedChild_hasTask (node : DeliveryNode)
    : ∃ occurrence owners producer payload,
        TaskAt (failedChild node) occurrence owners producer payload
        ∧ payload.failure.isSome = true :=
  ⟨
    _,
    _,
    _,
    _,
    .executionGroup (.left (.right (Located.root (root := failedChild node)))),
    rfl
  ⟩

/-- Both streamed items succeed partially and keep their own failing deferred child.
Witness: the actual stream entries. A theorem requiring a failed item itself would miss
this ordinary bubbling case, since no item result is an error.
-/
example
    : match completed.work with
      | .combine (.combine (.combine _ (.stream _ items)) _) _ =>
          items.length = 2
          ∧ ∀ entry ∈ items,
              (∃ data errors, entry.1 = { result := .ok (data, errors) })
              ∧ ∃ occurrence owners producer payload,
                  TaskAt entry.2 occurrence owners producer payload
                  ∧ payload.failure.isSome = true
      | _ => False := by
  conv => pattern completed.work; cbv
  change 2 = 2 ∧ _
  constructor
  · rfl
  · intro entry member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    all_goals
      constructor
      · exact ⟨.object [], 0, rfl⟩
      · exact failedChild_hasTask _

/-- Mixed root reflection derives retained failure evidence instead of stipulating it.
Witness: the general executable theorem applied to an actual ordinary bubble; its
initial-error alternative is ruled out by the computed error-free initial result.
-/
example : FailedBelow [] completed.work := by
  have reflected := executeRoot_explains_failures schema resolvers [] 30 "Query"
    (.object "Query" 0) selections (by cbv) 0 2 (by cbv)
  rcases reflected with initialFailed | retained
  · obtain ⟨errors, impossible⟩ := initialFailed
    have success : completed.result = .ok ([("users", .list [])], 0) := by cbv
    change completed.result = .error errors at impossible
    simp [success] at impossible
  · exact retained

/-- Ordinary root-null positions are covered by actual mixed retained work.
Witness: the new general bubbling-root certificate, with no hand-picked failure scope.
-/
example (containers : Bool)
    : PreparedResponseCovers .null (selectionSetResultToResponse completed.result)
        completed.work containers := by
  exact preparedResponseCovers_bubblingRoot schema resolvers [] 30 "Query"
    (.object "Query" 0) selections (by cbv) 0 2 (by cbv) containers

/-- The bubbling-root certificate is universal over mixed syntax and resolver outcomes.
Witness: the executable reflection theorem, not the fixture's particular completion.
-/
example {ObjectRef : Type} (schema : Schema) (environment : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef) (selections : List Selection)
    (valid : SelectionSet.hasValidIncrementalArguments variables selections = true)
    (state errors : Nat)
    (bubbles
      : GraphQL.Execution.executeRootSelectionSet schema environment variables fuel
          parentType source (SelectionSet.eraseIncrementalDirectives selections)
        = .error errors)
    (containers : Bool)
    : let completed :=
        ((executeRootSelectionSetCore schema environment variables fuel
            parentType source selections).run
          state).1
      PreparedResponseCovers .null (selectionSetResultToResponse completed.result)
        completed.work containers :=
  preparedResponseCovers_bubblingRoot schema environment variables fuel parentType source
    selections valid state errors bubbles containers

/-- All conforming complete observations of the mixed fixture address ordinary root null.
Witness: actual query failure reflection, not a selected history, ID, or completion scope.
-/
example (createWorkQueue : Work → WorkQueue) (result : ExecutionObservation)
    (conforms
      : queryWorkQueueConforms createWorkQueue schema resolvers []
          { selectionSet := selections } 30 (.object "Query" 0))
    (outcome
      : queryOutcome createWorkQueue schema resolvers []
          { selectionSet := selections } 30 (.object "Query" 0) result)
    (initialZero : result.initialErrors = 0) (containers : Bool)
    : result.AddressesResponsePositions containers .null := by
  exact queryOutcome_addresses_nullReference schema resolvers []
    { selectionSet := selections } 30 (.object "Query" 0) createWorkQueue result (by cbv)
    conforms outcome initialZero (by cbv) containers

#print axioms executeRoot_explains_failures
#print axioms preparedResponseCovers_bubblingRoot
#print axioms queryOutcome_addresses_nullReference
#print axioms ResponsePositionsDeliveredOrFailed_of_nonbubblingComparison

end GraphQL.IncrementalDelivery.Tests.OrdinaryFailureReflection
