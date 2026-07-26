import Tests.GraphQL.Common

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

end Schema
end Tests
end GraphQL
