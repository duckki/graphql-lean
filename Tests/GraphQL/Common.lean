import GraphQL.Operation

namespace GraphQL
namespace Tests

def testStringFieldDefinition (name : Name) : FieldDefinition :=
  { name := name, outputType := .named "String", arguments := [] }

def testObjectFieldDefinition
    (name typeName : Name) (arguments : List InputValueDefinition := [])
    : FieldDefinition :=
  { name := name, outputType := .named typeName, arguments := arguments }

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

def sampleDuplicateArgumentQuery : Operation :=
  {
    name := some "DuplicateArgument"
    rootType := "Query"
    selectionSet :=
      [.field "hero" "hero"
        [
          { name := "episode", value := .enum "NEWHOPE" },
          { name := "episode", value := .enum "NEWHOPE" }
        ]
        []
        [.field "name" "name" [] [] []]]
  }

end Tests
end GraphQL
