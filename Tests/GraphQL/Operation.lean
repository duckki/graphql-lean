import Tests.GraphQL.Common

namespace GraphQL
namespace Tests
namespace Operation

theorem fieldsWithMissingResponseNameSmoke
    : SelectionSet.fieldsWithResponseName "name" sampleHeroQuery.selectionSet = [] := by
  rfl

theorem fieldsWithAliasResponseNameSmoke
    : SelectionSet.fieldsWithResponseName "mainHero" sampleHeroQuery.selectionSet
      = sampleHeroQuery.selectionSet := by
  rfl

theorem withoutFieldsWithAliasResponseNameSmoke
    : SelectionSet.withoutFieldSelectionsWithResponseName "mainHero"
        sampleHeroQuery.selectionSet
      = [] := by
  rfl

theorem mergeSelectionSetsSmoke
    : SelectionSet.mergeSelectionSets sampleHeroQuery.selectionSet
      = [.field "name" "name" [] [] []] := by
  rfl

theorem operationSizeSmoke
    : sampleHeroQuery.size = SelectionSet.size sampleHeroQuery.selectionSet := by
  rfl

end Operation
end Tests
end GraphQL
