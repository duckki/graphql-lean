import Tests.GraphQL.Common
import GraphQL.SchemaWellFormedness

namespace GraphQL
namespace Tests
namespace Schema

theorem lookupQueryTypeSmoke : (sampleSchema.lookupType "Query").isSome = true := by
  rfl

theorem lookupCharacterTypeSmoke
    : (sampleSchema.lookupType "Character").isSome = true := by
  rfl

theorem lookupFieldSmoke
    : (sampleSchema.lookupField "Character" "name").isSome = true := by
  rfl

theorem lookupMissingArgumentSmoke
    : (match sampleSchema.lookupField "Character" "name" with
        | some fieldDefinition =>
            Schema.lookupArgumentDefinition fieldDefinition.arguments "unused"
        | none => none)
      = none := by
  rfl

theorem fieldReturnTypeSmoke
    : sampleSchema.fieldReturnType? "Character" "name" = some "String" := by
  rfl

theorem possibleTypesObjectSmoke
    : sampleSchema.getPossibleTypes "Character" = ["Character"] := by
  rfl

theorem typeIncludesObjectSmoke
    : sampleSchema.typeIncludesObjectBool "Character" "Character" = true := by
  rfl

def nullableRecursiveInputSchema : Schema :=
  {
    queryType := "Query"
    types :=
      [.inputObject
        {
          name := "Recursive"
          inputFields := [{ name := "next", inputType := .named "Recursive" }]
        }]
  }

def nonNullRecursiveInputSchema : Schema :=
  {
    queryType := "Query"
    types :=
      [.inputObject
        {
          name := "Recursive"
          inputFields :=
            [{ name := "next", inputType := .nonNull (.named "Recursive") }]
        }]
  }

def recursiveDefaultInputSchema : Schema :=
  {
    queryType := "Query"
    types :=
      [.inputObject
        {
          name := "Recursive"
          inputFields :=
            [{
              name := "next"
              inputType := .named "Recursive"
              defaultValue := some (.object [])
            }]
        }]
  }

theorem nullableInputObjectRecursionIsValid
    : SchemaWellFormedness.inputObjectCircularReferencesValid
        nullableRecursiveInputSchema := by
  constructor <;> rfl

theorem nonNullSingularInputObjectRecursionIsInvalid
    : SchemaWellFormedness.inputObjectNonNullSingularCircularReferencesValidBool
        nonNullRecursiveInputSchema
      = false := by
  rfl

theorem recursiveInputObjectDefaultIsInvalid
    : SchemaWellFormedness.inputDefaultExpansionAcyclicBool recursiveDefaultInputSchema
      = false := by
  rfl

end Schema
end Tests
end GraphQL
