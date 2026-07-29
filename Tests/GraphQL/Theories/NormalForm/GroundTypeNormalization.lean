import Tests.GraphQL.Theories.NormalForm.Common
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Normality
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness

namespace GraphQL
namespace Tests
namespace NormalForm

open GraphQL.NormalForm
open GraphQL.NormalForm.GroundTypeNormalization

#check normalSelectionSetsEqualUpToReorderingSemanticallyEquivalent
#check selectionSetsSemanticallyEquivalent_of_equalUpToReordering
#check normalOperationsEqualUpToReorderingSemanticallyEquivalent
#check normal_operations_equalUpToReordering_semanticallyEquivalent
#check normalizeOperationsEqualUpToReorderingSemanticallyEquivalent
#check normalizeOperations_equalUpToReordering_semanticallyEquivalent
#check selectionSetsDataEquivalent_of_equalUpToReordering
#check normalOperationsSemanticallyEquivalentEqualUpToReordering
#check normal_operations_semanticallyEquivalent_equalUpToReordering
#check normalizeOperationUniqueUpToReordering
#check normalizeOperation_uniqueUpToReordering
#check normalizeOperation_operationVariablesUsed

/-! Ground-typed normalization smoke tests use `*InputQuery` and `*OutputSnapshot` pairs. -/

def objectFieldInputQuery : Operation :=
  query { field "hero" { field "id", field "name" } }

def objectFieldOutputSnapshot : Operation :=
  query { field "hero" { field "id", field "name" } }

theorem objectFieldGroundTypingSmoke
    : operationWellFormedBool objectFieldInputQuery = true
      ∧ operationWellFormedBool objectFieldOutputSnapshot = true
      ∧ operationEqBool
          (normalizeOperation groundTypingSchema objectFieldInputQuery)
          objectFieldOutputSnapshot
        = true := by
  native_decide

theorem groundObjectTypesForObjectSmoke
    : groundObjectTypesForType groundTypingSchema "Human" = ["Human"] := by
  rfl

theorem groundObjectTypesForInterfaceSmoke
    : groundObjectTypesForType groundTypingSchema "Character" = ["Human", "Droid"] := by
  rfl

def abstractFieldInputQuery : Operation :=
  query { field "search" { field "id", on "Human" { field "homePlanet" } } }

def abstractFieldOutputSnapshot : Operation :=
  query
    { field "search"
        { on "Human" { field "id", field "homePlanet" }, on "Droid" { field "id" } } }

theorem abstractFieldGroundTypingSmoke
    : operationWellFormedBool abstractFieldInputQuery = true
      ∧ operationWellFormedBool abstractFieldOutputSnapshot = true
      ∧ operationEqBool
          (normalizeOperation groundTypingSchema abstractFieldInputQuery)
          abstractFieldOutputSnapshot
        = true := by
  native_decide

def allBranchesFeasibleAbstractFieldInputQuery : Operation :=
  query { field "search" { field "id", field "name" } }

def duplicateFieldInputQuery : Operation :=
  query { field "hero" { field "id" }, field "hero" { field "name" } }

def duplicateFieldOutputSnapshot : Operation :=
  query { field "hero" { field "id", field "name" } }

theorem duplicateFieldGroundTypingSmoke
    : operationWellFormedBool duplicateFieldInputQuery = true
      ∧ operationWellFormedBool duplicateFieldOutputSnapshot = true
      ∧ operationEqBool
          (normalizeOperation groundTypingSchema duplicateFieldInputQuery)
          duplicateFieldOutputSnapshot
        = true := by
  native_decide

def aliasedDuplicateFieldInputQuery : Operation :=
  operationWith
    [
      .field "lead" "hero" [] [] [Selection.field "id" "id" [] [] []],
      .field "lead" "hero" [] [] [Selection.field "name" "name" [] [] []]
    ]

def aliasedDuplicateFieldOutputSnapshot : Operation :=
  operationWith
    [.field "lead" "hero" [] []
      [Selection.field "id" "id" [] [] [], Selection.field "name" "name" [] [] []]]

theorem aliasedDuplicateFieldGroundTypingSmoke
    : operationWellFormedBool aliasedDuplicateFieldInputQuery = true
      ∧ operationWellFormedBool aliasedDuplicateFieldOutputSnapshot = true
      ∧ operationEqBool
          (normalizeOperation groundTypingSchema aliasedDuplicateFieldInputQuery)
          aliasedDuplicateFieldOutputSnapshot
        = true := by
  native_decide

def untypedInlineFragmentInputQuery : Operation :=
  query { spread { field "hero" { field "id" } } }

def untypedInlineFragmentOutputSnapshot : Operation :=
  query { field "hero" { field "id" } }

theorem untypedInlineFragmentGroundTypingSmoke
    : operationWellFormedBool untypedInlineFragmentInputQuery = true
      ∧ operationWellFormedBool untypedInlineFragmentOutputSnapshot = true
      ∧ operationEqBool
          (normalizeOperation groundTypingSchema untypedInlineFragmentInputQuery)
          untypedInlineFragmentOutputSnapshot
        = true := by
  native_decide

def nonOverlappingInlineFragmentInputQuery : Operation :=
  query { field "hero" { field "id", on "Droid" { field "primaryFunction" } } }

def nonOverlappingInlineFragmentOutputSnapshot : Operation :=
  query { field "hero" { field "id" } }

theorem nonOverlappingInlineFragmentGroundTypingSmoke
    : operationWellFormedBool nonOverlappingInlineFragmentInputQuery = true
      ∧ operationWellFormedBool nonOverlappingInlineFragmentOutputSnapshot = true
      ∧ operationEqBool
          (normalizeOperation groundTypingSchema nonOverlappingInlineFragmentInputQuery)
          nonOverlappingInlineFragmentOutputSnapshot
        = true := by
  native_decide

theorem strictTypeConditionFeasibilitySmoke
    : operationTypeConditionFeasible groundTypingSchema
        allBranchesFeasibleAbstractFieldInputQuery
      ∧ ¬ operationTypeConditionFeasible groundTypingSchema abstractFieldInputQuery
      ∧ ¬ operationTypeConditionFeasible groundTypingSchema
            nonOverlappingInlineFragmentInputQuery := by
  have hqueryPossible :
      groundTypingSchema.getPossibleTypes "Query" = ["Query"] := by
    native_decide
  have hcharacterPossible :
      groundTypingSchema.getPossibleTypes "Character" = ["Human", "Droid"] := by
    native_decide
  have hhumanPossible :
      groundTypingSchema.getPossibleTypes "Human" = ["Human"] := by
    native_decide
  have hdroidPossible :
      groundTypingSchema.getPossibleTypes "Droid" = ["Droid"] := by
    native_decide
  have hsearchLookup :
      groundTypingSchema.lookupField "Query" "search"
        = some (objectFieldDefinition "search" "Character") := by
    rfl
  have hheroLookup :
      groundTypingSchema.lookupField "Query" "hero"
        = some (objectFieldDefinition "hero" "Human") := by
    rfl
  have hqueryRoot : groundTypingSchema.queryType = "Query" := by
    rfl
  simp [operationTypeConditionFeasible, selectionSetTypeConditionFeasible,
    selectionTypeConditionFeasible, typeConditionStackFeasible,
    allBranchesFeasibleAbstractFieldInputQuery, abstractFieldInputQuery,
    nonOverlappingInlineFragmentInputQuery, Operation.rootType,
    OperationType.rootType,
    objectFieldDefinition, operationWith,
    TypeRef.namedType,
    hqueryRoot, hqueryPossible, hcharacterPossible, hhumanPossible, hdroidPossible,
    hsearchLookup, hheroLookup]

def abstractFieldEmptyGroundBranchInputQuery : Operation :=
  query { field "search" { on "Human" { field "homePlanet" } } }

def abstractFieldEmptyGroundBranchOutputSnapshot : Operation :=
  query { field "search" { on "Human" { field "homePlanet" } } }

theorem abstractFieldEmptyGroundBranchSmoke
    : operationWellFormedBool abstractFieldEmptyGroundBranchInputQuery = true
      ∧ operationWellFormedBool abstractFieldEmptyGroundBranchOutputSnapshot = true
      ∧ operationEqBool
          (normalizeOperation groundTypingSchema abstractFieldEmptyGroundBranchInputQuery)
          abstractFieldEmptyGroundBranchOutputSnapshot
        = true := by
  native_decide

def emptyInterfaceSchema : Schema :=
  {
    queryType := rootType
    types :=
      [
        .object
          {
            name := rootType
            fields :=
              [
                objectFieldDefinition "empty" "EmptyInterface",
                stringFieldDefinition "name"
              ]
            interfaces := []
          },
        .interface
          {
            name := "EmptyInterface"
            fields := [stringFieldDefinition "id"]
            interfaces := []
          }
      ]
  }

def emptyInterfaceFieldInputQuery : Operation :=
  query { field "empty" { field "id" }, field "name" }

def emptyInterfaceFieldOutputSnapshot : Operation :=
  query { field "empty" {}, field "name" }

theorem emptyInterfaceFieldRetainedSmoke
    : operationWellFormedBool emptyInterfaceFieldInputQuery = true
      ∧ operationEqBool
          (normalizeOperation emptyInterfaceSchema emptyInterfaceFieldInputQuery)
          emptyInterfaceFieldOutputSnapshot
        = true := by
  native_decide

def emptyInterfaceOnlyFieldInputQuery : Operation :=
  query { field "empty" { field "id" } }

def emptyInterfaceOnlyFieldOutputSnapshot : Operation :=
  query { field "empty" {} }

theorem emptyInterfaceOnlyFieldRetainedSmoke
    : operationWellFormedBool emptyInterfaceOnlyFieldInputQuery = true
      ∧ operationEqBool
          (normalizeOperation emptyInterfaceSchema emptyInterfaceOnlyFieldInputQuery)
          emptyInterfaceOnlyFieldOutputSnapshot
        = true := by
  native_decide

theorem normalizedSmokeInputsAreNormal
    (hschema : SchemaWellFormedness.schemaWellFormed groundTypingSchema)
    (hobjectValid
      : Validation.operationDefinitionValid groundTypingSchema objectFieldInputQuery)
    (habstractValid
      : Validation.operationDefinitionValid groundTypingSchema abstractFieldInputQuery)
    (hduplicateValid
      : Validation.operationDefinitionValid groundTypingSchema duplicateFieldInputQuery)
    (haliasedValid
      : Validation.operationDefinitionValid groundTypingSchema
          aliasedDuplicateFieldInputQuery)
    (huntypedValid
      : Validation.operationDefinitionValid groundTypingSchema
          untypedInlineFragmentInputQuery)
    (hnonOverlappingValid
      : Validation.operationDefinitionValid groundTypingSchema
          nonOverlappingInlineFragmentInputQuery)
    (hemptyBranchValid
      : Validation.operationDefinitionValid groundTypingSchema
          abstractFieldEmptyGroundBranchInputQuery)
    : operationNormal groundTypingSchema
        (normalizeOperation groundTypingSchema objectFieldInputQuery)
      ∧ operationNormal groundTypingSchema
          (normalizeOperation groundTypingSchema abstractFieldInputQuery)
      ∧ operationNormal groundTypingSchema
          (normalizeOperation groundTypingSchema duplicateFieldInputQuery)
      ∧ operationNormal groundTypingSchema
          (normalizeOperation groundTypingSchema aliasedDuplicateFieldInputQuery)
      ∧ operationNormal groundTypingSchema
          (normalizeOperation groundTypingSchema untypedInlineFragmentInputQuery)
      ∧ operationNormal groundTypingSchema
          (normalizeOperation groundTypingSchema nonOverlappingInlineFragmentInputQuery)
      ∧ operationNormal groundTypingSchema
          (normalizeOperation groundTypingSchema
            abstractFieldEmptyGroundBranchInputQuery) := by
  exact ⟨
    normalizeOperation_normal groundTypingSchema objectFieldInputQuery
      hschema hobjectValid,
    normalizeOperation_normal groundTypingSchema abstractFieldInputQuery
      hschema habstractValid,
    normalizeOperation_normal groundTypingSchema duplicateFieldInputQuery
      hschema hduplicateValid,
    normalizeOperation_normal groundTypingSchema aliasedDuplicateFieldInputQuery
      hschema haliasedValid,
    normalizeOperation_normal groundTypingSchema untypedInlineFragmentInputQuery
      hschema huntypedValid,
    normalizeOperation_normal groundTypingSchema
      nonOverlappingInlineFragmentInputQuery hschema hnonOverlappingValid,
    normalizeOperation_normal groundTypingSchema
      abstractFieldEmptyGroundBranchInputQuery hschema hemptyBranchValid⟩

end NormalForm
end Tests
end GraphQL
