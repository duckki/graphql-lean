import Tests.GraphQL.Common

namespace GraphQL
namespace Tests
namespace Operation

open scoped SyntacticEquivalence

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

theorem inputObjectSyntacticallyEquivalentBoolIgnoresFieldOrderSmoke
    : InputValue.syntacticallyEquivalentBool
        (.object [("first", .int 1), ("second", .string "two")])
        (.object [("second", .string "two"), ("first", .int 1)])
      = true := by
  rfl

theorem inputObjectSyntacticallyEquivalentDecidableSmoke
    : (.object [("first", .int 1), ("second", .string "two")] : InputValue)
      ≡ (.object [("second", .string "two"), ("first", .int 1)]) := by
  native_decide

theorem argumentsSyntacticallyEquivalentBoolIgnoresArgumentOrderSmoke
    : Argument.argumentsSyntacticallyEquivalentBool
        [
          { name := "first", value := .int 1 },
          { name := "second", value := .string "two" }
        ]
        [
          { name := "second", value := .string "two" },
          { name := "first", value := .int 1 }
        ]
      = true := by
  rfl

theorem argumentsSyntacticallyEquivalentDecidableSmoke
    : ([
          { name := "first", value := .int 1 },
          { name := "second", value := .string "two" }
        ]
        : List Argument)
      ≡ [
        { name := "second", value := .string "two" },
        { name := "first", value := .int 1 }
      ] := by
  native_decide

theorem argumentsSyntacticallyEquivalentBoolRejectsMissingArgumentSmoke
    : Argument.argumentsSyntacticallyEquivalentBool []
        [{ name := "first", value := .int 1 }]
      = false := by
  rfl

end Operation
end Tests
end GraphQL
