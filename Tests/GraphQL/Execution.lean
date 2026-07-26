import GraphQL.Execution

namespace GraphQL
namespace Tests
namespace Execution

#check GraphQL.Execution.selectionSetResultToResponse

def genericUnitObject : GraphQL.Execution.ResolverValue :=
  .object "Query" ()

theorem genericUnitObjectSmoke
    : genericUnitObject = GraphQL.Execution.ResolverValue.object "Query" () := by
  rfl

def objectConstructorUsesConcreteRef : PUnit -> GraphQL.Execution.ResolverValue PUnit :=
  GraphQL.Execution.ResolverValue.object (ObjectRef := PUnit) "Query"

mutual
  def responseEqBool
      : GraphQL.Execution.ResponseValue -> GraphQL.Execution.ResponseValue -> Bool
    | .null, .null => true
    | .scalar left, .scalar right => left == right
    | .object left, .object right => responseFieldsEqBool left right
    | .list left, .list right => responseListEqBool left right
    | _, _ => false

  def responseListEqBool
      : List GraphQL.Execution.ResponseValue -> List GraphQL.Execution.ResponseValue
        -> Bool
    | [], [] => true
    | left :: lefts, right :: rights =>
        responseEqBool left right && responseListEqBool lefts rights
    | _, _ => false

  def responseFieldsEqBool
      : List (Name × GraphQL.Execution.ResponseValue)
        -> List (Name × GraphQL.Execution.ResponseValue) -> Bool
    | [], [] => true
    | (leftName, leftValue) :: lefts, (rightName, rightValue) :: rights =>
        (leftName == rightName)
        && responseEqBool leftValue rightValue
        && responseFieldsEqBool lefts rights
    | _, _ => false
end

def testStringFieldDefinition (name : Name) : FieldDefinition :=
  { name := name, outputType := .named "String", arguments := [] }

def testNonNullStringFieldDefinition (name : Name) : FieldDefinition :=
  { name := name, outputType := .nonNull (.named "String"), arguments := [] }

def testObjectFieldDefinition
    (name typeName : Name) (arguments : List InputValueDefinition := [])
    : FieldDefinition :=
  { name := name, outputType := .named typeName, arguments := arguments }

def testNonNullObjectFieldDefinition
    (name typeName : Name) (arguments : List InputValueDefinition := [])
    : FieldDefinition :=
  { name := name, outputType := .nonNull (.named typeName), arguments := arguments }

def testEpisodeArgumentDefinition : InputValueDefinition :=
  { name := "episode", inputType := .named "Episode" }

def sampleSchema : Schema :=
  {
    queryType := "Query"
    types :=
      [
        .enum { name := "Episode", values := ["NEWHOPE"] },
        .object
          {
            name := "Query"
            fields :=
              [
                testObjectFieldDefinition "hero" "Character"
                  [testEpisodeArgumentDefinition],
                testStringFieldDefinition "name",
                { name := "age", outputType := .named "Int" }
              ]
            interfaces := []
          },
        .object
          {
            name := "Character"
            fields :=
              [
                testStringFieldDefinition "name",
                testObjectFieldDefinition "friends" "Character"
              ]
            interfaces := []
          }
      ]
  }

def sampleHeroQuery : Operation :=
  {
    name := some "HeroName"
    rootType := "Query"
    selectionSet :=
      [.field "mainHero" "hero" [] [] [.field "name" "name" [] [] []]]
  }

def sampleResolvers : GraphQL.Execution.Resolvers :=
  { resolve := fun parentType fieldName _arguments _source =>
      some <|
        match parentType, fieldName with
        | "Query", "hero" => .object "Character" ()
        | "Character", "name" => .scalar "Leia"
        | _, _ => .null
    resolve_argumentsEquivalent := by
      intros
      rfl }

theorem executeHeroQuerySmoke
    : responseEqBool
        (GraphQL.Execution.executeQuery sampleSchema sampleResolvers []
          sampleHeroQuery
          (GraphQL.Execution.ResolverValue.object "Query" ())).data
        (.object [("mainHero", .object [("name", .scalar "Leia")])])
      = true := by
  native_decide

def sampleErrorResolvers : GraphQL.Execution.Resolvers :=
  { resolve := fun parentType fieldName _arguments _source =>
      match parentType, fieldName with
      | "Query", "hero" => some (.object "Character" ())
      | "Character", "name" => none
      | _, _ => some .null
    resolve_argumentsEquivalent := by
      intros
      rfl }

theorem executeHeroQueryErrorCountSmoke
    : let response :=
        GraphQL.Execution.executeQuery sampleSchema sampleErrorResolvers []
          sampleHeroQuery
          (GraphQL.Execution.ResolverValue.object "Query" ())
      response.errors = 1
      ∧ responseEqBool response.data (.object [("mainHero", .object [("name", .null)])])
        = true := by
  native_decide

def nestedNonNullSchema : Schema :=
  {
    queryType := "Query"
    types :=
      [
        .object
          {
            name := "Query"
            fields :=
              [testObjectFieldDefinition "hero" "Character"]
            interfaces := []
          },
        .object
          {
            name := "Character"
            fields :=
              [testNonNullStringFieldDefinition "name"]
            interfaces := []
          }
      ]
  }

def rootNonNullSchema : Schema :=
  {
    queryType := "Query"
    types :=
      [
        .object
          {
            name := "Query"
            fields :=
              [testNonNullObjectFieldDefinition "hero" "Character"]
            interfaces := []
          },
        .object
          {
            name := "Character"
            fields :=
              [testNonNullStringFieldDefinition "name"]
            interfaces := []
          }
      ]
  }

def nonNullNameErrorResolvers : GraphQL.Execution.Resolvers :=
  { resolve := fun parentType fieldName _arguments _source =>
      match parentType, fieldName with
      | "Query", "hero" => some (.object "Character" ())
      | "Character", "name" => none
      | _, _ => some .null
    resolve_argumentsEquivalent := by
      intros
      rfl }

def nonNullNameNullResolvers : GraphQL.Execution.Resolvers :=
  { resolve := fun parentType fieldName _arguments _source =>
      match parentType, fieldName with
      | "Query", "hero" => some (.object "Character" ())
      | "Character", "name" => some .null
      | _, _ => some .null
    resolve_argumentsEquivalent := by
      intros
      rfl }

theorem executeNestedNonNullBubblesToNullableParentSmoke
    : let response :=
        GraphQL.Execution.executeQuery nestedNonNullSchema
          nonNullNameErrorResolvers [] sampleHeroQuery
          (GraphQL.Execution.ResolverValue.object "Query" ())
      response.errors = 1
      ∧ responseEqBool response.data (.object [("mainHero", .null)]) = true := by
  native_decide

theorem executeNestedNonNullBubblesToRootSmoke
    : let response :=
        GraphQL.Execution.executeQuery rootNonNullSchema
          nonNullNameErrorResolvers [] sampleHeroQuery
          (GraphQL.Execution.ResolverValue.object "Query" ())
      response.errors = 1 ∧ responseEqBool response.data .null = true := by
  native_decide

theorem executeExplicitNullForNonNullFieldCountsErrorSmoke
    : let response :=
        GraphQL.Execution.executeQuery nestedNonNullSchema
          nonNullNameNullResolvers [] sampleHeroQuery
          (GraphQL.Execution.ResolverValue.object "Query" ())
      response.errors = 1
      ∧ responseEqBool response.data (.object [("mainHero", .null)]) = true := by
  native_decide

theorem collectSubfieldsMatchesGroupedSelections
    (field : GraphQL.Execution.ExecutableField)
    (fields : List GraphQL.Execution.ExecutableField)
    : GraphQL.Execution.collectSubfields sampleSchema [] "Query"
        (GraphQL.Execution.ResolverValue.object (ObjectRef := PUnit) "Query" ())
        (field :: fields)
      = GraphQL.Execution.mergeExecutableGroups
          (GraphQL.Execution.collectFields sampleSchema [] "Query"
            (GraphQL.Execution.ResolverValue.object (ObjectRef := PUnit) "Query" ())
            field.selectionSet)
          (GraphQL.Execution.collectSubfields sampleSchema [] "Query"
            (GraphQL.Execution.ResolverValue.object (ObjectRef := PUnit) "Query" ())
            fields) := by
  rfl

theorem executeRootSelectionSetSmoke
    : (match GraphQL.Execution.executeRootSelectionSet sampleSchema sampleResolvers []
              (GraphQL.Execution.executeQueryFuelBound sampleHeroQuery)
              "Query"
              (GraphQL.Execution.ResolverValue.object "Query" ())
              sampleHeroQuery.selectionSet with
        | .ok (fields, _errors) =>
            responseEqBool (.object fields)
              (.object [("mainHero", .object [("name", .scalar "Leia")])])
        | .error _errors => false)
      = true := by
  native_decide

end Execution
end Tests
end GraphQL
