import GraphQL.Algorithms.ExecutionUngrouped
import Tests.GraphQL.Execution

namespace GraphQL
namespace Tests
namespace ExecutionUngrouped

open GraphQL.Tests.Execution

def duplicateHeroMergedSubfieldsQuery : Operation :=
  {
    name := some "DuplicateHeroMergedSubfields"
    selectionSet :=
      [
        .field "mainHero" "hero" [] [] [.field "name" "name" [] [] []],
        .field "mainHero" "hero" [] []
          [.field "friends" "friends" [] [] [.field "name" "name" [] [] []]]
      ]
  }

def duplicateRootNameQuery : Operation :=
  {
    name := some "DuplicateRootName"
    selectionSet :=
      [.field "name" "name" [] [] [], .field "name" "name" [] [] []]
  }

def duplicateHeroNullBubbleSchema : Schema :=
  {
    queryType := "Query"
    types :=
      [
        .object
          {
            name := "Query"
            fields := [testObjectFieldDefinition "hero" "Character"]
            interfaces := []
          },
        .object
          {
            name := "Character"
            fields :=
              [
                testNonNullStringFieldDefinition "name",
                testNonNullStringFieldDefinition "age"
              ]
            interfaces := []
          }
      ]
  }

def duplicateHeroLaterNullBubbleSchema : Schema :=
  {
    queryType := "Query"
    types :=
      [
        .object
          {
            name := "Query"
            fields := [testObjectFieldDefinition "hero" "Character"]
            interfaces := []
          },
        .object
          {
            name := "Character"
            fields :=
              [testStringFieldDefinition "name", testNonNullStringFieldDefinition "age"]
            interfaces := []
          }
      ]
  }

def duplicateHeroNullBubbleQuery : Operation :=
  {
    name := some "DuplicateHeroNullBubble"
    selectionSet :=
      [
        .field "hero" "hero" [] [] [.field "name" "name" [] [] []],
        .field "hero" "hero" [] [] [.field "age" "age" [] [] []]
      ]
  }

def cancelSiblingAfterRootBubbleSchema : Schema :=
  {
    queryType := "Query"
    types :=
      [.object
        {
          name := "Query"
          fields :=
            [testNonNullStringFieldDefinition "a", testStringFieldDefinition "b"]
          interfaces := []
        }]
  }

def cancelSiblingAfterRootBubbleQuery : Operation :=
  {
    name := some "CancelSiblingAfterRootBubble"
    selectionSet :=
      [.field "a" "a" [] [] [], .field "b" "b" [] [] []]
  }

def sampleResolversWithFriends : GraphQL.Execution.Resolvers :=
  { resolve := fun parentType fieldName _arguments _source =>
      some <|
        match parentType, fieldName with
        | "Query", "hero" => .object "Character" ()
        | "Character", "name" => .scalar "Leia"
        | "Character", "friends" => .object "Character" ()
        | _, _ => .null
    resolve_argumentsEquivalent := by
      intros
      rfl }

def nullBubblingDuplicateResolvers : GraphQL.Execution.Resolvers :=
  { resolve := fun parentType fieldName _arguments _source =>
      match parentType, fieldName with
      | "Query", "hero" => some (.object "Character" ())
      | "Character", "name" => none
      | "Character", "age" => none
      | _, _ => some .null
    resolve_argumentsEquivalent := by
      intros
      rfl }

def laterNullBubblingDuplicateResolvers : GraphQL.Execution.Resolvers :=
  { resolve := fun parentType fieldName _arguments _source =>
      match parentType, fieldName with
      | "Query", "hero" => some (.object "Character" ())
      | "Character", "name" => some (.scalar "Leia")
      | "Character", "age" => none
      | _, _ => some .null
    resolve_argumentsEquivalent := by
      intros
      rfl }

def nullSiblingResolvers : GraphQL.Execution.Resolvers :=
  { resolve := fun _parentType _fieldName _arguments _source => none
    resolve_argumentsEquivalent := by
      intros
      rfl }

theorem duplicateCompositeFieldCompletesIntoPreviousSmoke
    : let source := GraphQL.Execution.ResolverValue.object "Query" ()
      let spec :=
        GraphQL.Execution.executeQuery sampleSchema sampleResolversWithFriends []
          duplicateHeroMergedSubfieldsQuery source
      let ungrouped :=
        GraphQL.Algorithms.ExecutionUngrouped.executeQuery sampleSchema
          sampleResolversWithFriends [] duplicateHeroMergedSubfieldsQuery source
      spec.errors = ungrouped.errors
      ∧ responseEqBool spec.data ungrouped.data = true
      ∧ responseEqBool ungrouped.data
          (.object
            [(
              "mainHero",
              .object
                [
                  ("name", .scalar "Leia"),
                  ("friends", .object [("name", .scalar "Leia")])
                ]
            )])
        = true := by
  native_decide

theorem duplicateRootFieldFuelZeroCountsResponseNameOnceSmoke
    : let source := GraphQL.Execution.ResolverValue.object "Query" ()
      let spec :=
        GraphQL.Execution.executeQueryWithFuel sampleSchema sampleResolvers []
          duplicateRootNameQuery 0 source
      let ungrouped :=
        GraphQL.Algorithms.ExecutionUngrouped.executeQueryWithFuel sampleSchema
          sampleResolvers [] duplicateRootNameQuery 0 source
      spec.errors = 1
      ∧ spec.errors = ungrouped.errors
      ∧ responseEqBool spec.data ungrouped.data = true := by
  native_decide

theorem duplicateCompositeNullBubbleErrorsDifferSmoke
    : let source := GraphQL.Execution.ResolverValue.object "Query" ()
      let spec :=
        GraphQL.Execution.executeQueryWithFuel duplicateHeroNullBubbleSchema
          nullBubblingDuplicateResolvers [] duplicateHeroNullBubbleQuery 5 source
      let ungrouped :=
        GraphQL.Algorithms.ExecutionUngrouped.executeQueryWithFuel
          duplicateHeroNullBubbleSchema nullBubblingDuplicateResolvers []
          duplicateHeroNullBubbleQuery 5 source
      spec.errors = 2
      ∧ ungrouped.errors = 1
      ∧ responseEqBool spec.data ungrouped.data = true
      ∧ responseEqBool spec.data (.object [("hero", .null)]) = true := by
  native_decide

theorem siblingAfterRootBubbleCancelledSmoke
    : let source := GraphQL.Execution.ResolverValue.object "Query" ()
      let spec :=
        GraphQL.Execution.executeQueryWithFuel cancelSiblingAfterRootBubbleSchema
          nullSiblingResolvers [] cancelSiblingAfterRootBubbleQuery 5 source
      let ungrouped :=
        GraphQL.Algorithms.ExecutionUngrouped.executeQueryWithFuel
          cancelSiblingAfterRootBubbleSchema nullSiblingResolvers []
          cancelSiblingAfterRootBubbleQuery 5 source
      spec.errors = 2
      ∧ ungrouped.errors = 1
      ∧ responseEqBool spec.data ungrouped.data = true
      ∧ responseEqBool spec.data .null = true := by
  native_decide

theorem duplicateCompositeLaterNullBubbleOverridesPreviousDataSmoke
    : let source := GraphQL.Execution.ResolverValue.object "Query" ()
      let spec :=
        GraphQL.Execution.executeQueryWithFuel duplicateHeroLaterNullBubbleSchema
          laterNullBubblingDuplicateResolvers [] duplicateHeroNullBubbleQuery 5
          source
      let ungrouped :=
        GraphQL.Algorithms.ExecutionUngrouped.executeQueryWithFuel
          duplicateHeroLaterNullBubbleSchema laterNullBubblingDuplicateResolvers []
          duplicateHeroNullBubbleQuery 5 source
      spec.errors = 1
      ∧ ungrouped.errors = 1
      ∧ responseEqBool spec.data (.object [("hero", .null)]) = true
      ∧ responseEqBool spec.data ungrouped.data = true := by
  native_decide

theorem executeQueryUsesVariableDefaultSmoke
    : responseEqBool
        (GraphQL.Algorithms.ExecutionUngrouped.executeQuery sampleSchema
          rootNameResolvers [] variableDefaultQuery
          (GraphQL.Execution.ResolverValue.object "Query" ())).data
        (.object [("name", .scalar "Query")])
      = true := by
  native_decide

end ExecutionUngrouped
end Tests
end GraphQL
