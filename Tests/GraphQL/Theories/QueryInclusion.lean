import GraphQL.Theories.QueryInclusion
import Tests.GraphQL.Common

namespace GraphQL.Tests.QueryInclusion

open GraphQL.QueryInclusion

theorem includesBoolReference_reflSmoke
    : includesBoolReference sampleSchema sampleHeroQuery sampleHeroQuery = true := by
  native_decide

def nestedConditionalHeroQuery : Operation :=
  {
    variableDefinitions :=
      [{ name := "showName", typeRef := .named "Boolean" }]
    selectionSet :=
      [.field "mainHero" "hero" [] []
        [.field "name" "name" [] [.include (.variable "showName")] []]]
  }

-- Identical nested queries are included under both values of `showName`.
theorem includesBoolReference_nestedConditionalSmoke
    : includesBoolReference sampleSchema nestedConditionalHeroQuery
        nestedConditionalHeroQuery
      = true := by
  native_decide

def regionalSchema : Schema :=
  {
    queryType := "Query"
    types :=
      [
        .object
          {
            name := "Query"
            fields := [testObjectFieldDefinition "character" "Character"]
          },
        .interface
          {
            name := "Character"
            fields := [testStringFieldDefinition "id"]
          },
        .object
          {
            name := "Human"
            fields :=
              [testStringFieldDefinition "id", testStringFieldDefinition "home"]
            interfaces := ["Character"]
          },
        .object
          {
            name := "Droid"
            fields :=
              [testStringFieldDefinition "id", testStringFieldDefinition "primary"]
            interfaces := ["Character"]
          }
      ]
  }

def regionalCharacterQuery : Operation :=
  {
    selectionSet :=
      [.field "character" "character" [] []
        [
          .field "id" "id" [] [] [],
          .inlineFragment (some "Human") [] [.field "home" "home" [] [] []],
          .inlineFragment (some "Droid") [] [.field "primary" "primary" [] [] []]
        ]]
  }

-- Reflexivity holds across concrete runtime types and their inline fragments.
theorem includesBoolReference_regionalReflexiveSmoke
    : includesBoolReference regionalSchema regionalCharacterQuery regionalCharacterQuery
      = true := by
  native_decide

def regionalIdQuery : Operation :=
  {
    selectionSet :=
      [.field "character" "character" [] [] [.field "id" "id" [] [] []]]
  }

def regionalIdWithHumanExtraQuery : Operation :=
  {
    selectionSet :=
      [.field "character" "character" [] []
        [
          .field "id" "id" [] [] [],
          .inlineFragment (some "Human") [] [.field "home" "home" [] [] []]
        ]]
  }

-- Additional left selections do not prevent directional inclusion.
theorem includesBoolReference_extraLeftSelectionSmoke
    : includesBoolReference regionalSchema regionalIdWithHumanExtraQuery regionalIdQuery
      = true := by
  native_decide

def booleanWeakLeftQuery : Operation :=
  {
    variableDefinitions :=
      [{ name := "enabled", typeRef := .named "Boolean" }]
    selectionSet :=
      [
        .field "age" "age" [] [] [],
        .field "support" "name" [] [.include (.variable "enabled")] []
      ]
  }

def booleanStrongRightQuery : Operation :=
  {
    variableDefinitions :=
      [{ name := "enabled", typeRef := .named "Boolean" }]
    selectionSet :=
      [.field "age" "age" [] [.include (.variable "enabled")] []]
  }

-- The unconditional left `age` field covers both right-hand Boolean cases.
theorem includesBoolReference_scalarConditionSmoke
    : includesBoolReference sampleSchema booleanWeakLeftQuery booleanStrongRightQuery
      = true := by
  native_decide

def unconditionalAgeQuery : Operation :=
  { selectionSet := [.field "age" "age" [] [] []] }

def rightConditionalAgeQuery : Operation :=
  {
    variableDefinitions :=
      [{ name := "rightEnabled", typeRef := .nonNull (.named "Boolean") }]
    selectionSet :=
      [.field "age" "age" [] [.include (.variable "rightEnabled")] []]
  }

def leftConditionalAgeQuery : Operation :=
  {
    variableDefinitions :=
      [{ name := "leftEnabled", typeRef := .nonNull (.named "Boolean") }]
    selectionSet :=
      [.field "age" "age" [] [.include (.variable "leftEnabled")] []]
  }

-- The unconditional left field covers both values of the right-only variable.
theorem includesBoolReference_allowsDifferentBooleanDefinitionsSmoke
    : includesBoolReference sampleSchema unconditionalAgeQuery rightConditionalAgeQuery
      = true := by
  native_decide

-- Distinct Boolean supports remain independent: `rightEnabled = true` and
-- `leftEnabled = false` exposes the missing left response field.
theorem includesBoolReference_distinctBooleanConditionsRemainIndependentSmoke
    : includesBoolReference sampleSchema leftConditionalAgeQuery rightConditionalAgeQuery
      = false := by
  native_decide

def conditionalAgeQueryWithDefault (defaultValue : Bool) : Operation :=
  {
    variableDefinitions :=
      [{
        name := "enabled"
        typeRef := .named "Boolean"
        defaultValue := some (.boolean defaultValue)
      }]
    selectionSet :=
      [.field "age" "age" [] [.include (.variable "enabled")] []]
  }

-- A shared condition variable may be omitted at runtime, so its defaults must agree
-- before the static inclusion analysis is applicable.
theorem includesBoolReference_rejectsDifferentSharedBooleanDefaultsSmoke
    : includesBoolReference sampleSchema (conditionalAgeQueryWithDefault true)
        (conditionalAgeQueryWithDefault false)
      = false := by
  native_decide

def reorderedVariableDefinitionsQuery (reverse : Bool) : Operation :=
  let enabled : VariableDefinition :=
    {
      name := "enabled"
      typeRef := .named "Boolean"
      defaultValue := some (.boolean true)
    }
  let marker : VariableDefinition :=
    {
      name := "marker"
      typeRef := .named "Boolean"
    }
  {
    variableDefinitions := if reverse then [marker, enabled] else [enabled, marker]
    selectionSet :=
      [
        .field "age" "age" [] [.include (.variable "enabled")] [],
        .field "support" "name" [] [.include (.variable "marker")] []
      ]
  }

theorem includesBoolReference_allowsReorderedVariableDefinitionsSmoke
    : includesBoolReference sampleSchema (reorderedVariableDefinitionsQuery false)
        (reorderedVariableDefinitionsQuery true)
      = true := by
  native_decide

theorem includesBoolReference_allowsExclusiveVariableDefaultSmoke
    : includesBoolReference sampleSchema unconditionalAgeQuery
        (conditionalAgeQueryWithDefault true)
      = true := by
  native_decide

def complementaryBooleanLeftQuery : Operation :=
  {
    variableDefinitions :=
      [
        { name := "enabled", typeRef := .named "Boolean" },
        { name := "marker", typeRef := .named "Boolean" }
      ]
    selectionSet :=
      [
        .field "age" "age" [] [.include (.variable "enabled")] [],
        .field "age" "age" [] [.skip (.variable "enabled")] [],
        .field "age" "age" [] [.include (.variable "marker")] [],
        .field "support" "name" [] [.include (.variable "enabled")] []
      ]
  }

def complementaryBooleanRightQuery : Operation :=
  {
    variableDefinitions := complementaryBooleanLeftQuery.variableDefinitions
    selectionSet :=
      [
        .field "age" "age" [] [] [],
        .field "age" "age" [] [.include (.variable "marker")] [],
        .field "support" "name" [] [.include (.variable "enabled")] []
      ]
  }

-- Complementary @include and @skip clauses cover an unconditional field.
theorem includesBoolReference_complementaryClausesSmoke
    : includesBoolReference sampleSchema complementaryBooleanLeftQuery
        complementaryBooleanRightQuery
      = true := by
  native_decide

def leftBranchVariables : List VariableDefinition :=
  [{ name := "leftBranch", typeRef := .nonNull (.named "Boolean") }]

def guardedParentLeftSelectionSet : List Selection :=
  [.field "hero" "hero" [] [.include (.variable "leftBranch")]
    [.field "name" "name" [] [] []]]

def unconditionalParentRightSelectionSet : List Selection :=
  [.field "hero" "hero" [] [] [.field "name" "name" [] [] []]]

def guardedParentLeftQuery : Operation :=
  {
    variableDefinitions := leftBranchVariables
    selectionSet := guardedParentLeftSelectionSet
  }

def unconditionalParentRightQuery : Operation :=
  { selectionSet := unconditionalParentRightSelectionSet }

def contradictoryChildLeftSelectionSet : List Selection :=
  [.field "hero" "hero" [] [.include (.variable "leftBranch")]
    [.field "name" "name" [] [] []]]

def contradictoryChildRightSelectionSet : List Selection :=
  [.field "hero" "hero" [] [.include (.variable "leftBranch")]
    [
      .field "name" "name" [] [] [],
      .field "impossible" "name" [] [.skip (.variable "leftBranch")] []
    ]]

def contradictoryChildLeftQuery : Operation :=
  {
    variableDefinitions := leftBranchVariables
    selectionSet := contradictoryChildLeftSelectionSet
  }

def contradictoryChildRightQuery : Operation :=
  {
    variableDefinitions := leftBranchVariables
    selectionSet := contradictoryChildRightSelectionSet
  }

-- A conditional parent cannot cover an unconditional right-hand field.
theorem includesBoolReference_rejectsGuardedCoverageGapSmoke
    : includesBoolReference sampleSchema guardedParentLeftQuery
        unconditionalParentRightQuery
      = false := by
  native_decide

-- A child excluded by its parent condition adds no selected path.
theorem includesBoolReference_dropsContradictoryChildSmoke
    : includesBoolReference sampleSchema contradictoryChildLeftQuery
        contradictoryChildRightQuery
      = true := by
  native_decide

def covariantRegionalSchema : Schema :=
  {
    queryType := "Query"
    types :=
      [
        .object
          {
            name := "Query"
            fields := [testObjectFieldDefinition "character" "Character"]
          },
        .interface
          {
            name := "Character"
            fields :=
              [
                testStringFieldDefinition "id",
                testObjectFieldDefinition "companion" "Character"
              ]
          },
        .object
          {
            name := "Human"
            fields :=
              [
                testStringFieldDefinition "id",
                testObjectFieldDefinition "companion" "Human"
              ]
            interfaces := ["Character"]
          },
        .object
          {
            name := "Droid"
            fields :=
              [
                testStringFieldDefinition "id",
                testStringFieldDefinition "primaryFunction",
                testObjectFieldDefinition "companion" "Droid"
              ]
            interfaces := ["Character"]
          }
      ]
  }

def covariantRegionalQuery : Operation :=
  {
    selectionSet :=
      [.field "character" "character" [] []
        [.field "companion" "companion" [] [] [.field "id" "id" [] [] []]]]
  }

def broaderCompositeTypeConditionLeftSelectionSet : List Selection :=
  [.inlineFragment (some "Character") []
    [.field "companion" "companion" [] []
      [.field "id" "id" [] [] [], .field "extra" "id" [] [] []]]]

def narrowerCompositeTypeConditionRightSelectionSet : List Selection :=
  [.inlineFragment (some "Human") []
    [.field "companion" "companion" [] [] [.field "id" "id" [] [] []]]]

-- The broader Character guard covers the narrower Human fragment.
def broaderCompositeTypeConditionLeftQuery : Operation :=
  {
    selectionSet :=
      [.field "character" "character" [] [] broaderCompositeTypeConditionLeftSelectionSet]
  }

def narrowerCompositeTypeConditionRightQuery : Operation :=
  {
    selectionSet :=
      [.field "character" "character" [] []
        narrowerCompositeTypeConditionRightSelectionSet]
  }

theorem includesBoolReference_broaderCompositeTypeConditionSmoke
    : includesBoolReference covariantRegionalSchema broaderCompositeTypeConditionLeftQuery
        narrowerCompositeTypeConditionRightQuery
      = true := by
  native_decide

-- Covariant return types preserve reflexivity; missing child fields still fail.
theorem includesBoolReference_covariantReflexiveSmoke
    : includesBoolReference covariantRegionalSchema covariantRegionalQuery
        covariantRegionalQuery
      = true := by
  native_decide

def covariantRegionalLeftQuery : Operation :=
  {
    selectionSet :=
      [.field "character" "character" [] []
        [.field "companion" "companion" [] [] [.field "id" "id" [] [] []]]]
  }

def covariantRegionalRightQuery : Operation :=
  {
    selectionSet :=
      [.field "character" "character" [] []
        [.field "companion" "companion" [] []
          [
            .field "id" "id" [] [] [],
            .inlineFragment (some "Droid") []
              [.field "primaryFunction" "primaryFunction" [] [] []]
          ]]]
  }

-- The active parent nodes are identical for `Human` and `Droid`, but the covariant
-- `companion` return contributes both concrete child types. The checker must not
-- choose only the first parent-region representative and miss the Droid-only field.
theorem includesBoolReference_covariantUnionRejectsMissingFieldSmoke
    : includesBoolReference covariantRegionalSchema covariantRegionalLeftQuery
        covariantRegionalRightQuery
      = false := by
  native_decide

def heroQueryWithExtraRootField : Operation :=
  {
    selectionSet :=
      [
        .field "mainHero" "hero" [] [] [.field "name" "name" [] [] []],
        .field "age" "age" [] [] []
      ]
  }

theorem includesBoolReference_extraFieldsSmoke
    : includesBoolReference sampleSchema heroQueryWithExtraRootField sampleHeroQuery
      = true := by
  native_decide

theorem includesBoolReference_directionalMissingExtraFieldSmoke
    : includesBoolReference sampleSchema sampleHeroQuery heroQueryWithExtraRootField
      = false := by
  native_decide

def sameAliasDifferentResolverQuery : Operation :=
  { selectionSet := [.field "mainHero" "name" [] [] []] }

theorem includesBoolReference_rejectsDifferentResolverCallSmoke
    : includesBoolReference sampleSchema sameAliasDifferentResolverQuery sampleHeroQuery
      = false := by
  native_decide

def heroQueryWithVariableDefault (defaultValue : ConstInputValue) : Operation :=
  {
    variableDefinitions :=
      [{ name := "argument", typeRef := .named "Int", defaultValue := some defaultValue }]
    selectionSet := sampleHeroQuery.selectionSet
  }

theorem includesBoolReference_rejectsDifferentVariableDefaultsSmoke
    : includesBoolReference sampleSchema
        (heroQueryWithVariableDefault (.int 1))
        (heroQueryWithVariableDefault (.int 2))
      = false := by
  native_decide

theorem variableDefinitionsSyntacticallyEquivalentDecidableSmoke
    : GraphQL.variableDefinitionsSyntacticallyEquivalent
        (heroQueryWithVariableDefault (.int 1)).variableDefinitions
        (heroQueryWithVariableDefault (.int 1)).variableDefinitions := by
  native_decide

theorem variableDefinitionsSyntacticallyEquivalentAllowsReorderingSmoke
    : GraphQL.variableDefinitionsSyntacticallyEquivalent
        [
          {
            name := "first"
            typeRef := .nonNull (.named "Int")
            defaultValue := some (.int 1)
          },
          {
            name := "second"
            typeRef := .named "Boolean"
          }
        ]
        [
          {
            name := "second"
            typeRef := .named "Boolean"
          },
          {
            name := "first"
            typeRef := .nonNull (.named "Int")
            defaultValue := some (.int 1)
          }
        ] := by
  native_decide

theorem sharedVariableDefinitionsCompatibilityAllowsReorderingSmoke
    : GraphQL.QueryInclusion.sharedVariableDefinitionsSyntacticallyCompatible
        [
          {
            name := "first"
            typeRef := .nonNull (.named "Int")
            defaultValue := some (.int 1)
          },
          {
            name := "second"
            typeRef := .named "Boolean"
          }
        ]
        [
          {
            name := "second"
            typeRef := .named "Boolean"
          },
          {
            name := "first"
            typeRef := .nonNull (.named "Int")
            defaultValue := some (.int 1)
          }
        ] := by
  native_decide

theorem sharedVariableDefinitionsCompatibilityRejectsDifferentTypesSmoke
    : GraphQL.QueryInclusion.sharedVariableDefinitionsSyntacticallyCompatibleBool
        [{ name := "shared", typeRef := .named "Boolean" }]
        [{ name := "shared", typeRef := .named "Int" }]
      = false := by
  native_decide

theorem sharedVariableDefinitionsCompatibilityAllowsExclusiveDefinitionsSmoke
    : GraphQL.QueryInclusion.sharedVariableDefinitionsSyntacticallyCompatible
        [{ name := "leftOnly", typeRef := .nonNull (.named "Boolean") }]
        [{ name := "rightOnly", typeRef := .nonNull (.named "Input") }] := by
  native_decide

theorem includesBoolReference_rejectsDifferentSharedVariableTypesSmoke
    : includesBoolReference sampleSchema
        {
          variableDefinitions := [{ name := "shared", typeRef := .named "Boolean" }]
          selectionSet := sampleHeroQuery.selectionSet
        }
        {
          variableDefinitions := [{ name := "shared", typeRef := .named "Int" }]
          selectionSet := sampleHeroQuery.selectionSet
        }
      = false := by
  native_decide

theorem includesBoolReference_allowsExclusiveVariableDefinitionsSmoke
    : includesBoolReference sampleSchema
        {
          variableDefinitions := [{ name := "leftOnly", typeRef := .named "Boolean" }]
          selectionSet := sampleHeroQuery.selectionSet
        }
        {
          variableDefinitions := [{ name := "rightOnly", typeRef := .named "Int" }]
          selectionSet := sampleHeroQuery.selectionSet
        }
      = true := by
  native_decide

def emptyCompositeSchema : Schema :=
  {
    queryType := "Query"
    types :=
      [
        .object
          {
            name := "Query"
            fields :=
              [
                { name := "value", outputType := .named "String" },
                { name := "empty", outputType := .nonNull (.named "Empty") },
                { name := "nullableEmpty", outputType := .named "Empty" },
                {
                  name := "emptyList",
                  outputType := .nonNull (.list (.nonNull (.named "Empty")))
                }
              ]
          },
        .interface
          {
            name := "Empty"
            fields := [{ name := "name", outputType := .named "String" }]
          }
      ]
  }

def feasibleValueSelection : List Selection :=
  [.field "value" "value" [] [] []]

def infeasibleEmptySelection : List Selection :=
  [.field "empty" "empty" [] [] [.field "name" "name" [] [] []]]

-- The checker remains structural even when one selected composite type has no possible
-- object type.
theorem selectionSetIncludes_rejectsMissingInfeasibleRightSmoke
    : selectionSetIncludesBoolWithFuel emptyCompositeSchema 2 "Query" []
        feasibleValueSelection infeasibleEmptySelection
      = false := by
  native_decide

theorem selectionSetIncludes_rejectsMissingFeasibleRightSmoke
    : selectionSetIncludesBoolWithFuel emptyCompositeSchema 2 "Query" []
        infeasibleEmptySelection feasibleValueSelection
      = false := by
  native_decide

def uninhabitedChildAliasLeft : Operation :=
  { selectionSet := [.field "empty" "empty" [] [] [.field "x" "name" [] [] []]] }

def uninhabitedChildAliasRight : Operation :=
  { selectionSet := [.field "empty" "empty" [] [] [.field "name" "name" [] [] []]] }

-- The root field path matches, while no child path can exist under the uninhabited type.
theorem includesBoolReference_ignoresUninhabitedChildAliasSmoke
    : includesBoolReference emptyCompositeSchema uninhabitedChildAliasLeft
        uninhabitedChildAliasRight
      = true := by
  native_decide

-----------------------------------------------------------------------------------------
-- Resolver-call identity with infeasible child fragments
-----------------------------------------------------------------------------------------

-- Pairwise fragment overlaps are nonempty (`O ∩ T1 = {A}`, `T1 ∩ T2 = {B}`), but no
-- object type is in all three of `O`, `T1`, `T2`. A doubly nested fragment therefore
-- collects nothing at every runtime type reachable from an `O`-typed field.
def responseUnobservableSchema : Schema :=
  {
    queryType := "Query"
    types :=
      [
        .object
          {
            name := "Query"
            fields :=
              [
                { name := "p1", outputType := .nonNull (.named "O") },
                { name := "p2", outputType := .nonNull (.named "O") }
              ]
          },
        .interface { name := "O", fields := [] },
        .interface { name := "T1", fields := [] },
        .interface
          { name := "T2", fields := [{ name := "x", outputType := .named "String" }] },
        .object { name := "A", fields := [], interfaces := ["O", "T1"] },
        .object
          {
            name := "B"
            fields := [{ name := "x", outputType := .named "String" }]
            interfaces := ["T1", "T2"]
          },
        .object
          {
            name := "C"
            fields := [{ name := "x", outputType := .named "String" }]
            interfaces := ["T2", "O"]
          }
      ]
  }

def responseUnobservableBody : List Selection :=
  [.inlineFragment (some "T1") []
    [.inlineFragment (some "T2") [] [.field "x" "x" [] [] []]]]

def responseUnobservableLeft : Operation :=
  { name := some "L", selectionSet := [.field "p" "p1" [] [] responseUnobservableBody] }

def responseUnobservableRight : Operation :=
  { name := some "R", selectionSet := [.field "p" "p2" [] [] responseUnobservableBody] }

-- The checker rejects on resolver-call provenance (`p1` versus `p2`).
theorem responseUnobservable_checkerRejectsSmoke
    : includesBoolReference responseUnobservableSchema responseUnobservableLeft
        responseUnobservableRight
      = false := by
  native_decide

end GraphQL.Tests.QueryInclusion
