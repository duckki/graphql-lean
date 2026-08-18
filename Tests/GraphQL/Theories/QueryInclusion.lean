import GraphQL.Theories.QueryInclusion
import Proofs.GraphQL.Theories.QueryInclusion
import Tests.GraphQL.Common

namespace GraphQL.Tests.QueryInclusion

open GraphQL.QueryInclusion
open GraphQL.AnnotatedExecution

def heroCall : ResolvedFieldProvenance :=
  {
    parentType := "Query"
    fieldName := "hero"
    originalArguments := []
    coercedArguments := .success []
  }

def hero : AnnotatedResponseField :=
  .resolved "mainHero" heroCall (.scalar "R2-D2")

theorem sameFieldProvenanceDecidableSmoke : sameFieldProvenance heroCall heroCall := by
  native_decide

example
    : annotatedResponseValueIncludes (.object "Query" [hero])
        (.object "Query" [hero]) := by
  simp only [annotatedResponseValueIncludes]
  intro rightName rightCall rightValue hmember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmember
  injection hmember with hname hcall hvalue
  subst rightName
  subst rightCall
  subst rightValue
  refine ⟨"mainHero", heroCall, .scalar "R2-D2", by simp [hero], rfl, ?_, ?_⟩
  · exact (sameFieldProvenance_iff _ _).mpr
      ⟨rfl, rfl, by simp [heroCall, Argument.argumentsEquivalent]⟩
  · simp only [annotatedResponseValueIncludes]

def villainCall : ResolvedFieldProvenance :=
  {
    parentType := "Query"
    fieldName := "villain"
    originalArguments := []
    coercedArguments := .success []
  }

def wrongProvenance : AnnotatedResponseField :=
  .resolved "mainHero" villainCall (.scalar "Vader")

example
    : ¬ annotatedResponseValueIncludes (.object "Query" [wrongProvenance])
          (.object "Query" [hero]) := by
  intro h
  simp only [annotatedResponseValueIncludes] at h
  rcases h "mainHero" heroCall (.scalar "R2-D2") (by simp [hero]) with
    ⟨candidateName, candidateCall, candidateValue, hmember, hname, hcall, _⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmember
  injection hmember with hcandidateName hcandidateCall hcandidateValue
  subst candidateName
  subst candidateCall
  subst candidateValue
  rcases (sameFieldProvenance_iff _ _).mp hcall with ⟨_, hfield, _⟩
  simp [villainCall, heroCall] at hfield

theorem includesBool_reflSmoke
    : includesBool sampleSchema sampleHeroQuery sampleHeroQuery = true := by
  native_decide

def nestedConditionalHeroQuery : Operation :=
  {
    variableDefinitions :=
      [{ name := "showName", typeRef := .named "Boolean" }]
    selectionSet :=
      [.field "mainHero" "hero" [] []
        [.field "name" "name" [] [.include (.variable "showName")] []]]
  }

-- Identical nested syntax is accepted by the recursive syntax shortcut without
-- enumerating `showName`.
theorem includesBool_nestedSyntacticShortcutSmoke
    : includesBool sampleSchema nestedConditionalHeroQuery nestedConditionalHeroQuery
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

-- A reflexive regional query is a positive smoke test for the recursive shortcut.
-- Region-search behavior is tested directly below after guarded groups are available.
theorem includesBool_regionalReflexiveShortcutSmoke
    : includesBool regionalSchema regionalCharacterQuery regionalCharacterQuery
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

-- The exact right child selection is present on the left, so the additional Human
-- occurrence does not prevent the directional syntax shortcut.
theorem includesBool_extraLeftSelectionShortcutSmoke
    : includesBool regionalSchema regionalIdWithHumanExtraQuery regionalIdQuery
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

-- The unconditional left `age` clause symbolically covers the conditional right clause.
theorem includesBool_scalarConditionShortcutSmoke
    : includesBool sampleSchema booleanWeakLeftQuery booleanStrongRightQuery = true := by
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

-- A right-only Boolean definition can be caller-assigned as a free variable in the
-- semantic relation. The unconditional left field covers both values explored by the
-- static checker.
theorem includesBool_allowsDifferentBooleanDefinitionsSmoke
    : includesBool sampleSchema unconditionalAgeQuery rightConditionalAgeQuery = true
      ∧ includesBoolReference sampleSchema unconditionalAgeQuery rightConditionalAgeQuery
        = true := by
  native_decide

-- Distinct Boolean supports remain independent: `rightEnabled = true` and
-- `leftEnabled = false` exposes the missing left response field.
theorem includesBool_distinctBooleanConditionsRemainIndependentSmoke
    : includesBool sampleSchema leftConditionalAgeQuery rightConditionalAgeQuery
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
theorem includesBool_rejectsDifferentSharedBooleanDefaultsSmoke
    : includesBool sampleSchema (conditionalAgeQueryWithDefault true)
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

theorem includesBool_allowsReorderedVariableDefinitionsSmoke
    : includesBool sampleSchema (reorderedVariableDefinitionsQuery false)
        (reorderedVariableDefinitionsQuery true)
      = true := by
  native_decide

theorem includesBool_allowsExclusiveVariableDefaultSmoke
    : includesBool sampleSchema unconditionalAgeQuery
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

def guardedGroupForSelectionSet (schema : Schema) (parentType responseName : Name)
    (selectionSet : List Selection)
    : GuardedFieldGroup :=
  let groups :=
    guardedFieldGroups (SelectionConditions.ofSelectionSet schema parentType selectionSet)
  (findGuardedFieldGroup? responseName groups).getD { responseName, entries := [] }

def regionalIdWithHumanDuplicateSelectionSet : List Selection :=
  [
    .field "id" "id" [] [] [],
    .inlineFragment (some "Human") [] [.field "id" "id" [] [] []]
  ]

-- Calls the general region checker directly, bypassing both local shortcuts. The
-- Human-only duplicate contributes a left-only boundary, while the merged resolver call
-- still includes the unconditional right field in both Human and Droid regions.
theorem guardedFieldGroup_typeRegionRefinementSmoke
    : let left :=
        guardedGroupForSelectionSet regionalSchema "Character" "id"
          regionalIdWithHumanDuplicateSelectionSet
      let right :=
        guardedGroupForSelectionSet regionalSchema "Character" "id"
          [.field "id" "id" [] [] []]
      guardedFieldGroupIncludesWithFuel regionalSchema 1 none [] [] left right
        (guardedFieldGroupTypeRegions ["Human", "Droid"] left right)
      = true := by
  native_decide

-- Calls the assignment-enumerating group checker directly. The false branch has no
-- right field; the true branch compares the two `age` resolver calls.
theorem guardedFieldGroup_incrementalBooleanSplitSmoke
    : let left :=
        guardedGroupForSelectionSet sampleSchema "Query" "age"
          booleanWeakLeftQuery.selectionSet
      let right :=
        guardedGroupForSelectionSet sampleSchema "Query" "age"
          booleanStrongRightQuery.selectionSet
      guardedFieldGroupIncludesWithFuel sampleSchema 1 (some "Query") []
        (guardedFieldGroupBooleanVariables left right) left right
        (guardedFieldGroupTypeRegions ["Query"] left right)
      = true := by
  native_decide

-- One-pass grouping preserves first-response occurrence order and source order within
-- the repeated `age` group.
theorem guardedFieldGroups_onePassOrderSmoke
    : let groups :=
        guardedFieldGroups
          (SelectionConditions.ofSelectionSet sampleSchema "Query"
            [
              .field "age" "age" [] [] [],
              .field "support" "name" [] [] [],
              .field "age" "age" [] [.include (.boolean true)] []
            ])
      groups.map GuardedFieldGroup.responseName = ["age", "support"]
      ∧ (groups.head?.map fun group => group.entries.length) = some 2 := by
  native_decide

-- Complementary clauses cover the unconditional right field. The unrelated `marker`
-- occurrence remains in the same response group, but no Boolean assignment is
-- enumerated by the symbolic shortcut.
theorem guardedScalarField_complementaryClausesSmoke
    : guardedScalarFieldIncludesBool sampleSchema 1 (some "Query")
        (guardedGroupForSelectionSet sampleSchema "Query" "age"
          complementaryBooleanLeftQuery.selectionSet)
        (guardedGroupForSelectionSet sampleSchema "Query" "age"
          complementaryBooleanRightQuery.selectionSet)
        [["Query"]]
      = true := by
  native_decide

theorem includesBool_complementaryClausesSmoke
    : includesBool sampleSchema complementaryBooleanLeftQuery
        complementaryBooleanRightQuery
      = true := by
  native_decide

theorem booleanConditionCoveredByBool_complementarySmoke
    : SelectionConditions.booleanConditionCoveredByBool []
        [[.positive "enabled"], [.negative "enabled"]]
      = true := by
  native_decide

theorem booleanConditionCoveredByBool_gapSmoke
    : SelectionConditions.booleanConditionCoveredByBool [] [[.positive "enabled"]]
      = false := by
  native_decide

def broaderTypeConditionLeftSelectionSet : List Selection :=
  [.inlineFragment (some "Character") [] [.field "id" "id" [] [] []]]

def narrowerTypeConditionRightSelectionSet : List Selection :=
  [.inlineFragment (some "Human") [] [.field "id" "id" [] [] []]]

-- The flattened left condition covers the right's narrower Human region even though
-- the two inline-fragment AST nodes are not structurally identical.
theorem guardedScalarField_broaderTypeConditionSmoke
    : let left :=
        guardedGroupForSelectionSet regionalSchema "Character" "id"
          broaderTypeConditionLeftSelectionSet
      let right :=
        guardedGroupForSelectionSet regionalSchema "Character" "id"
          narrowerTypeConditionRightSelectionSet
      guardedScalarFieldIncludesBool regionalSchema 1 none left right
        (guardedFieldGroupTypeRegions ["Human", "Droid"] left right)
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

-- The richer local shortcut also follows one-to-one composite fields. Here the left
-- Character guard covers Human, and its companion child syntactically includes the
-- right child.
theorem guardedCompositeField_broaderTypeConditionSmoke
    : let left :=
        guardedGroupForSelectionSet covariantRegionalSchema "Character"
          "companion" broaderCompositeTypeConditionLeftSelectionSet
      let right :=
        guardedGroupForSelectionSet covariantRegionalSchema "Character"
          "companion" narrowerCompositeTypeConditionRightSelectionSet
      guardedCompositeFieldIncludesBool covariantRegionalSchema 2 none left right
        (guardedFieldGroupTypeRegions ["Human", "Droid"] left right)
      = true := by
  native_decide

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

theorem includesBool_broaderCompositeTypeConditionSmoke
    : includesBool covariantRegionalSchema broaderCompositeTypeConditionLeftQuery
        narrowerCompositeTypeConditionRightQuery
      = true := by
  native_decide

-- Reflexive covariant syntax is handled by the recursive shortcut. The following
-- negative case forces the general checker to retain the full child type union.
theorem includesBool_covariantReflexiveShortcutSmoke
    : includesBool covariantRegionalSchema covariantRegionalQuery covariantRegionalQuery
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
theorem includesBool_covariantUnionRejectsMissingFieldSmoke
    : includesBool covariantRegionalSchema covariantRegionalLeftQuery
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

theorem includesBool_extraFieldsSmoke
    : includesBool sampleSchema heroQueryWithExtraRootField sampleHeroQuery = true := by
  native_decide

theorem includesBool_directionalMissingExtraFieldSmoke
    : includesBool sampleSchema sampleHeroQuery heroQueryWithExtraRootField = false := by
  native_decide

def syntacticShortcutLeft : List Selection :=
  [.field "hero" "hero" [] [] [.field "id" "id" [] [] [], .field "name" "name" [] [] []]]

def syntacticShortcutRight : List Selection :=
  [.field "hero" "hero" [] [] [.field "id" "id" [] [] []]]

-- Exact right syntax is a directional witness even when the left has extra response
-- fields. Two units of fuel are required for the `hero.id` response path.
theorem syntacticInclusionShortcutSmoke
    : selectionSetSyntacticInclusionShortcutBool 2 syntacticShortcutLeft
        syntacticShortcutRight
      = true := by
  native_decide

theorem syntacticInclusionShortcutRespectsFuelSmoke
    : selectionSetSyntacticInclusionShortcutBool 1 syntacticShortcutLeft
        syntacticShortcutRight
      = false := by
  native_decide

-- Repeated right syntax is harmless because GraphQL merges fields by response name.
theorem syntacticInclusionShortcutDuplicateRightSmoke
    : selectionSetSyntacticInclusionShortcutBool 1
        [.field "id" "id" [] [] []]
        [.field "id" "id" [] [] [], .field "id" "id" [] [] []]
      = true := by
  native_decide

def sameAliasDifferentResolverQuery : Operation :=
  { selectionSet := [.field "mainHero" "name" [] [] []] }

theorem includesBool_rejectsDifferentResolverCallSmoke
    : includesBool sampleSchema sameAliasDifferentResolverQuery sampleHeroQuery
      = false := by
  native_decide

def heroQueryWithVariableDefault (defaultValue : ConstInputValue) : Operation :=
  {
    variableDefinitions :=
      [{ name := "argument", typeRef := .named "Int", defaultValue := some defaultValue }]
    selectionSet := sampleHeroQuery.selectionSet
  }

theorem includesBool_rejectsDifferentVariableDefaultsSmoke
    : includesBool sampleSchema
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

theorem includesBool_rejectsDifferentSharedVariableTypesSmoke
    : includesBool sampleSchema
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

theorem includesBool_allowsExclusiveVariableDefinitionsSmoke
    : includesBool sampleSchema
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

theorem includesBool_soundSmoke
    (hschema : SchemaWellFormedness.schemaWellFormed sampleSchema)
    (hvalid : Validation.operationDefinitionValid sampleSchema sampleHeroQuery)
    : includes sampleSchema sampleHeroQuery sampleHeroQuery :=
  includesBool_sound hschema hvalid hvalid includesBool_reflSmoke

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
                { name := "empty", outputType := .nonNull (.named "Empty") }
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
-- object type. Completeness excludes this case with an explicit operation assumption.
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

-----------------------------------------------------------------------------------------
-- Spec-level response-unobservable boundary
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

-- A resolver family may answer `p1` and `p2` with different concrete objects; under the
-- non-null wrapper, only objects in `O`'s possible types complete without an error.
def responseUnobservableResolvers : GraphQL.Execution.Resolvers :=
  {
    resolve :=
      fun parentType fieldName _arguments _source =>
        some
        <| match parentType, fieldName with
            | "Query", "p1" => .object "A" ()
            | "Query", "p2" => .object "C" ()
            | _, "x" => .scalar "never-collected"
            | _, _ => .null
    resolve_argumentsEquivalent := by
      intros
      rfl
  }

def responseUnobservableNullProbe : GraphQL.Execution.Resolvers :=
  {
    resolve :=
      fun parentType fieldName _arguments _source =>
        some
        <| match parentType, fieldName with
            | "Query", "p1" => .null
            | "Query", "p2" => .object "C" ()
            | _, _ => .null
    resolve_argumentsEquivalent := by
      intros
      rfl
  }

-- The checker rejects on resolver-call provenance (`p1` versus `p2`).
theorem responseUnobservable_checkerRejectsSmoke
    : includesBool responseUnobservableSchema responseUnobservableLeft
        responseUnobservableRight
      = false := by
  native_decide

mutual
  def unobservableResponseEqBool
      : GraphQL.Execution.ResponseValue -> GraphQL.Execution.ResponseValue -> Bool
    | .null, .null => true
    | .scalar left, .scalar right => left == right
    | .object left, .object right => unobservableResponseFieldsEqBool left right
    | .list left, .list right => unobservableResponseValuesEqBool left right
    | _, _ => false

  def unobservableResponseFieldsEqBool
      : List (Name × GraphQL.Execution.ResponseValue)
        -> List (Name × GraphQL.Execution.ResponseValue) -> Bool
    | [], [] => true
    | (leftName, leftValue) :: lefts, (rightName, rightValue) :: rights =>
        leftName == rightName
        && unobservableResponseEqBool leftValue rightValue
        && unobservableResponseFieldsEqBool lefts rights
    | _, _ => false

  def unobservableResponseValuesEqBool
      : List GraphQL.Execution.ResponseValue -> List GraphQL.Execution.ResponseValue
        -> Bool
    | [], [] => true
    | left :: lefts, right :: rights =>
        unobservableResponseEqBool left right
        && unobservableResponseValuesEqBool lefts rights
    | _, _ => false
end

-- Yet the spec responses cannot tell the operations apart: both produce `{p: {}}` even
-- when the two fields resolve to different concrete objects, so `includesUnannotated` holds for
-- this pair while the checker rejects. This is why `IncludesToIncludesUnannotated` has
-- no converse statement: plain responses cannot observe the differing resolver calls.
theorem responseUnobservable_equalResponsesSmoke
    : unobservableResponseEqBool
          (GraphQL.Execution.executeQuery responseUnobservableSchema
            responseUnobservableResolvers [] responseUnobservableLeft
            (.object "Query" ())).data
          (GraphQL.Execution.executeQuery responseUnobservableSchema
            responseUnobservableResolvers [] responseUnobservableRight
            (.object "Query" ())).data
        = true
      ∧ (GraphQL.Execution.executeQuery responseUnobservableSchema
          responseUnobservableResolvers [] responseUnobservableLeft
          (.object "Query" ())).errors
        = 0
      ∧ (GraphQL.Execution.executeQuery responseUnobservableSchema
          responseUnobservableResolvers [] responseUnobservableRight
          (.object "Query" ())).errors
        = 0 := by
  native_decide

-- Null-signaling cannot separate the two fields either: under the non-null wrapper a
-- null resolver result is an execution error, so no error-free distinguishing pair
-- exists.
theorem responseUnobservable_nullProbeErrorsSmoke
    : (GraphQL.Execution.executeQuery responseUnobservableSchema
        responseUnobservableNullProbe [] responseUnobservableLeft
        (.object "Query" ())).errors
      = 1 := by
  native_decide

end GraphQL.Tests.QueryInclusion
