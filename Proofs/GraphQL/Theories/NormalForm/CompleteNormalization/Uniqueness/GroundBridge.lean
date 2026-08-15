import Proofs.GraphQL.Execution.ArgumentCoercion
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Uniqueness.RestrictedSemantics
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Uniqueness.VariableIndependence
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.FocusedValidSeparation

/-!
Ground selection-set uniqueness bridge used by complete normalization uniqueness.
-/

namespace GraphQL

namespace NormalForm

namespace CompleteNormalization

theorem selectionSetEqualUpToReorderingWithCoercion_right_transport
    {schema : Schema} {leftValues rightValues : Execution.VariableValues}
    (hvalues : Execution.variableValuesCoercionEquivalent leftValues rightValues)
    {parentType : Name} {left right : List Selection}
    (hequal
      : SelectionSetEqualUpToReorderingWithCoercion schema leftValues leftValues
          parentType left right)
    : SelectionSetEqualUpToReorderingWithCoercion schema leftValues rightValues
        parentType left right := by
  refine SelectionSetEqualUpToReorderingWithCoercion.rec
    (motive_1 := fun parentType left right _hequal =>
      SelectionEqualUpToReorderingWithCoercion schema leftValues rightValues
        parentType left right)
    (motive_2 := fun parentType left right _hequal =>
      SelectionSetEqualUpToReorderingWithCoercion schema leftValues rightValues
        parentType left right)
    ?_ ?_ ?_ hequal
  · intro fieldParentType responseName fieldName leftArguments rightArguments
      directives leftSelectionSet rightSelectionSet fieldDefinition hlookup
      hcoercion _hchildren hchildren
    apply SelectionEqualUpToReorderingWithCoercion.field fieldParentType
      responseName fieldName directives fieldDefinition hlookup
    · have hcoerced :=
        Execution.coerceArgumentValues_equivalent_of_variableValuesCoercionEquivalent
          schema hvalues fieldDefinition.arguments rightArguments
      exact Execution.ArgumentCoercionResult.equivalent_trans hcoercion hcoerced
    · exact hchildren
  · intro fragmentParentType typeCondition directives leftSelectionSet
      rightSelectionSet _hchildren hchildren
    exact SelectionEqualUpToReorderingWithCoercion.inlineFragment
      fragmentParentType typeCondition directives hchildren
  · intro pairParentType pairLeft pairRight pairs hleft hright _hpairs hpairs
    exact SelectionSetEqualUpToReorderingWithCoercion.paired pairs hleft hright
      hpairs

theorem validNormalObjectSelectionSets_semanticallyEquivalent_equalUpToReordering
    {schema : Schema}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    {leftVariableValues rightVariableValues : Execution.VariableValues}
    {parentType : Name} {left right : List Selection}
    (hvalues
      : Execution.variableValuesCoercionEquivalent leftVariableValues rightVariableValues)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hleftValid
      : Validation.selectionSetValid schema leftVariableDefinitions parentType left)
    (hrightValid
      : Validation.selectionSetValid schema rightVariableDefinitions parentType right)
    (hleftCoercion
      : selectionSetArgumentsCoercible schema leftVariableValues parentType left)
    (hrightCoercion
      : selectionSetArgumentsCoercible schema rightVariableValues parentType right)
    (hleftFree : selectionSetDirectiveFree left)
    (hrightFree : selectionSetDirectiveFree right)
    (hleftNormal : selectionSetNormal schema parentType left)
    (hrightNormal : selectionSetNormal schema parentType right)
    (hobject : objectTypeNameBool schema parentType = true)
    (hsem
      : selectionSetsSemanticallyEquivalentAtVariableValues schema
          leftVariableValues rightVariableValues parentType left right)
    : SelectionSetEqualUpToReorderingWithCoercion schema leftVariableValues
        rightVariableValues parentType left right := by
  have hsemSame :
      selectionSetsSemanticallyEquivalentAtVariableValues schema
        leftVariableValues leftVariableValues parentType left right := by
    intro ObjectRef resolvers fuel source hsource
    have hrightExecution :
        Execution.executeSelectionSetAsResponse schema resolvers
            rightVariableValues fuel parentType source right
          = Execution.executeSelectionSetAsResponse schema resolvers
            leftVariableValues fuel parentType source right := by
      unfold Execution.executeSelectionSetAsResponse
      rw [executeSelectionSet_eq_of_variableValuesCoercionEquivalent schema
        resolvers (Execution.variableValuesCoercionEquivalent_symm hvalues)
        fuel parentType source right]
    rw [← hrightExecution]
    exact hsem resolvers fuel source hsource
  have hrightCoercionSame :
      selectionSetArgumentsCoercible schema leftVariableValues parentType right :=
    selectionSetArgumentsCoercible_of_variableValuesCoercionEquivalent
      hvalues parentType right hrightCoercion
  have hleftCoercionAll :
      selectionSetArgumentsCoercibleInPossibleTypes schema leftVariableValues
        parentType left :=
    GroundTypeNormalization.selectionSetArgumentsCoercibleInPossibleTypes_of_object
      hobject hleftCoercion
  have hrightCoercionAll :
      selectionSetArgumentsCoercibleInPossibleTypes schema leftVariableValues
        parentType right :=
    GroundTypeNormalization.selectionSetArgumentsCoercibleInPossibleTypes_of_object
      hobject hrightCoercionSame
  have hsame :
      SelectionSetEqualUpToReorderingWithCoercion schema leftVariableValues
        leftVariableValues parentType left right := by
    by_cases hequal :
        SelectionSetEqualUpToReorderingWithCoercion schema leftVariableValues
          leftVariableValues parentType left right
    · exact hequal
    · exfalso
      have hdiff :=
        GroundTypeNormalization.normalSelectionSetDiff_of_not_equal
          hleftFree hrightFree hleftNormal hrightNormal hequal
      rcases
          GroundTypeNormalization.selectionSetContextualRuntimeDataDiffWitnessWithFuelGe_of_valid_normal_coercion_diff
            hschema hleftValid hrightValid hleftCoercionAll hrightCoercionAll
            hleftFree hrightFree hleftNormal
            hrightNormal (supportSelectionSets := []) (minFuel := 0)
            (by simp) hdiff with
        ⟨runtimeType, hinclude, ObjectRef, resolvers, fuel, ref, _hfuel,
          _hsupport, hnotData⟩
      have hruntimeEq : runtimeType = parentType :=
        GroundTypeNormalization.typeIncludesObjectBool_eq_of_objectTypeNameBool_true
          schema hobject hinclude
      subst runtimeType
      have hsemantic := hsemSame resolvers fuel
        (Execution.ResolverValue.object parentType ref)
        ⟨parentType, ref, rfl, hinclude⟩
      exact hnotData hsemantic.1
  exact selectionSetEqualUpToReorderingWithCoercion_right_transport
    hvalues hsame

end CompleteNormalization

end NormalForm

end GraphQL
