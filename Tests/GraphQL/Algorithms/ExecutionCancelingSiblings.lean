import Proofs.GraphQL.Algorithms.ExecutionCancelingSiblings
import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Semantics.Final
import Tests.GraphQL.Algorithms.ExecutionUngrouped

namespace GraphQL
namespace Tests
namespace ExecutionCancelingSiblings

open GraphQL.Tests.Execution
open GraphQL.Tests.ExecutionUngrouped

theorem siblingAfterRootBubbleCancelledSmoke
    : let source := GraphQL.Execution.ResolverValue.object "Query" ()
      let spec :=
        GraphQL.Execution.executeQueryWithFuel cancelSiblingAfterRootBubbleSchema
          nullSiblingResolvers [] cancelSiblingAfterRootBubbleQuery 5 source
      let canceling :=
        GraphQL.Algorithms.ExecutionCancelingSiblings.executeQueryWithFuel
          cancelSiblingAfterRootBubbleSchema nullSiblingResolvers []
          cancelSiblingAfterRootBubbleQuery 5 source
      spec.errors = 2
      ∧ canceling.errors = 1
      ∧ responseEqBool spec.data canceling.data = true
      ∧ responseEqBool spec.data .null = true := by
  native_decide

theorem semanticPreservationStatementHasProofWitness
    : GraphQL.Algorithms.ExecutionCancelingSiblings.siblingCancelingExecutionPreservesSpecExecution
        cancelSiblingAfterRootBubbleSchema cancelSiblingAfterRootBubbleQuery :=
  GraphQL.Algorithms.ExecutionCancelingSiblings.siblingCancelingExecutionPreservesSpecExecution_proof
    cancelSiblingAfterRootBubbleSchema cancelSiblingAfterRootBubbleQuery

def interleavedDuplicateBeforeBubbleSchema : Schema :=
  {
    queryType := "Query"
    types :=
      [
        .object
          {
            name := "Query"
            fields :=
              [
                testObjectFieldDefinition "hero" "Character",
                testNonNullStringFieldDefinition "stop"
              ]
            interfaces := []
          },
        .object
          {
            name := "Character"
            fields :=
              [testStringFieldDefinition "name", testStringFieldDefinition "age"]
            interfaces := []
          }
      ]
  }

def interleavedDuplicateBeforeBubbleQuery : Operation :=
  {
    name := some "InterleavedDuplicateBeforeBubble"
    selectionSet :=
      [
        .field "hero" "hero" [] [] [.field "name" "name" [] [] []],
        .field "stop" "stop" [] [] [],
        .field "hero" "hero" [] [] [.field "age" "age" [] [] []]
      ]
  }

def interleavedDuplicateBeforeBubbleResolvers : GraphQL.Execution.Resolvers :=
  {
    resolve :=
      fun parentType fieldName _arguments _source =>
        match parentType, fieldName with
        | "Query", "hero" => some (.object "Character" ())
        | "Query", "stop" => none
        | "Character", "name" => some (.scalar "Leia")
        | "Character", "age" => none
        | _, _ => some .null
    resolve_argumentsEquivalent := by
      intros
      rfl
  }

-- Field collection executes both `hero` occurrences before `stop`, while
-- syntax-order ungrouped execution cancels the second occurrence after `stop`
-- bubbles. The responses therefore agree on data and error presence, but not
-- on the exact error count.
theorem interleavedDuplicateErrorCountsDifferSmoke
    : let source := GraphQL.Execution.ResolverValue.object "Query" ()
      let ungrouped :=
        GraphQL.Algorithms.ExecutionUngrouped.executeQueryWithFuel
          interleavedDuplicateBeforeBubbleSchema
          interleavedDuplicateBeforeBubbleResolvers []
          interleavedDuplicateBeforeBubbleQuery 5 source
      let canceling :=
        GraphQL.Algorithms.ExecutionCancelingSiblings.executeQueryWithFuel
          interleavedDuplicateBeforeBubbleSchema
          interleavedDuplicateBeforeBubbleResolvers []
          interleavedDuplicateBeforeBubbleQuery 5 source
      ungrouped.errors = 1
      ∧ canceling.errors = 2
      ∧ responseEqBool ungrouped.data canceling.data = true
      ∧ responseEqBool ungrouped.data .null = true := by
  native_decide

theorem uncachedUngroupedCancelingEquivalenceStatementHasProofWitness
    : GraphQL.Algorithms.ExecutionUngroupedUncached.ungroupedExecutionEquivalentToCancelingSiblingsExecution
        interleavedDuplicateBeforeBubbleSchema interleavedDuplicateBeforeBubbleQuery :=
  GraphQL.Algorithms.ExecutionUngroupedUncached.ungroupedExecutionEquivalentToCancelingSiblingsExecution_proof
    interleavedDuplicateBeforeBubbleSchema interleavedDuplicateBeforeBubbleQuery

end ExecutionCancelingSiblings
end Tests
end GraphQL
