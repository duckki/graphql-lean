import GraphQL.Algorithms.ExecutionUngrouped
import GraphQL.Algorithms.ExecutionUngroupedUncached
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
  {
    resolve :=
      fun parentType fieldName _arguments _source =>
        some
        <| match parentType, fieldName with
            | "Query", "hero" => .object "Character" ()
            | "Character", "name" => .scalar "Leia"
            | "Character", "friends" => .object "Character" ()
            | _, _ => .null
    resolve_argumentsEquivalent := by
      intros
      rfl
  }

def nullBubblingDuplicateResolvers : GraphQL.Execution.Resolvers :=
  {
    resolve :=
      fun parentType fieldName _arguments _source =>
        match parentType, fieldName with
        | "Query", "hero" => some (.object "Character" ())
        | "Character", "name" => none
        | "Character", "age" => none
        | _, _ => some .null
    resolve_argumentsEquivalent := by
      intros
      rfl
  }

def laterNullBubblingDuplicateResolvers : GraphQL.Execution.Resolvers :=
  {
    resolve :=
      fun parentType fieldName _arguments _source =>
        match parentType, fieldName with
        | "Query", "hero" => some (.object "Character" ())
        | "Character", "name" => some (.scalar "Leia")
        | "Character", "age" => none
        | _, _ => some .null
    resolve_argumentsEquivalent := by
      intros
      rfl
  }

def nullSiblingResolvers : GraphQL.Execution.Resolvers :=
  {
    resolve := fun _parentType _fieldName _arguments _source => none
    resolve_argumentsEquivalent := by
      intros
      rfl
  }

def sourceCachingSchema : Schema :=
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
            fields := [testStringFieldDefinition "name", testStringFieldDefinition "age"]
            interfaces := []
          }
      ]
  }

def sourceCachingQuery : Operation :=
  {
    name := some "SourceCaching"
    selectionSet :=
      [
        .field "hero" "hero" [] [] [.field "name" "name" [] [] []],
        .field "hero" "hero" [] [] [.field "age" "age" [] [] []]
      ]
  }

def sourceCachingResolvers : GraphQL.Execution.Resolvers String :=
  {
    resolve :=
      fun parentType fieldName _arguments source =>
        match parentType, fieldName, source with
        | "Query", "hero", _ => some (.object "Character" "leia-source")
        | "Character", "name", .object _typeName ref => some (.scalar ref)
        | "Character", "age", .object _typeName ref => some (.scalar (ref ++ "-age"))
        | _, _, _ => some .null
    resolve_argumentsEquivalent := by
      intros
      rfl
  }

def sourceCachingSource : GraphQL.Execution.ResolverValue String :=
  GraphQL.Execution.ResolverValue.object "Query" "root"

def sourceCachingVisit : GraphQL.Algorithms.ExecutionUngrouped.VisitResult String :=
  GraphQL.Algorithms.ExecutionUngrouped.visitSubfields
    sourceCachingSchema sourceCachingResolvers [] 8 "Query" sourceCachingSource
    sourceCachingQuery.selectionSet
    (GraphQL.Algorithms.ExecutionUngrouped.FieldCacheValue.object sourceCachingSource [])

def sourceCachingResponse : GraphQL.Execution.Response :=
  GraphQL.Algorithms.ExecutionUngrouped.executeQueryWithFuel
    sourceCachingSchema sourceCachingResolvers [] sourceCachingQuery 8 sourceCachingSource

def sourceCachingHeroFieldRetainsResolverSource : Bool :=
  match sourceCachingVisit.status, sourceCachingVisit.value with
  | .ok (_unit, _errors), .object _source fields =>
      match GraphQL.Algorithms.ExecutionUngrouped.lookupField? "hero" fields with
      | some (.object (.object "Character" "leia-source") _fields) => true
      | _ => false
  | _, _ => false

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

theorem duplicateCompositeFieldCachesSourceSmoke
    : sourceCachingHeroFieldRetainsResolverSource = true
      ∧ responseEqBool sourceCachingResponse.data
          (.object
            [(
              "hero",
              .object
                [("name", .scalar "leia-source"), ("age", .scalar "leia-source-age")]
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

theorem cachedUngroupedExecutorPassesCoercedArgumentsToGivenResolver
    : responseEqBool
        (GraphQL.Algorithms.ExecutionUngrouped.executeQuery coercedResolverSchema
          resolverArgumentPresenceResolvers [] omittedResolverArgumentOperation
          (GraphQL.Execution.ResolverValue.object "Query" ())).data
        (.object [("echo", .scalar "present")])
      = true := by
  native_decide

theorem uncachedUngroupedExecutorPassesCoercedArgumentsToGivenResolver
    : responseEqBool
        (GraphQL.Algorithms.ExecutionUngroupedUncached.executeQuery
          coercedResolverSchema resolverArgumentPresenceResolvers []
          omittedResolverArgumentOperation
          (GraphQL.Execution.ResolverValue.object "Query" ())).data
        (.object [("echo", .scalar "present")])
      = true := by
  native_decide

end ExecutionUngrouped
end Tests
end GraphQL
