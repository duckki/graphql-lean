import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Uniqueness.VariableIndependence
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.FocusedValidSeparation

/-!
Ground selection-set uniqueness bridge used by complete normalization uniqueness.
-/

namespace GraphQL

namespace NormalForm

namespace CompleteNormalization

theorem validNormalObjectSelectionSets_semanticallyEquivalent_equalUpToReordering
    {schema : Schema}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    {parentType : Name} {left right : List Selection}
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hleftValid
      : Validation.selectionSetValid schema leftVariableDefinitions parentType left)
    (hrightValid
      : Validation.selectionSetValid schema rightVariableDefinitions parentType right)
    (hleftFree : selectionSetDirectiveFree left)
    (hrightFree : selectionSetDirectiveFree right)
    (hleftNormal : selectionSetNormal schema parentType left)
    (hrightNormal : selectionSetNormal schema parentType right)
    (hobject : objectTypeNameBool schema parentType = true)
    (hsem : selectionSetsSemanticallyEquivalent schema parentType left right)
    : SelectionSetEqualUpToReordering left right := by
  by_cases hequal : SelectionSetEqualUpToReordering left right
  · exact hequal
  · have hdiff :
        GroundTypeNormalization.NormalSelectionSetDiff schema parentType
          left right :=
      GroundTypeNormalization.normalSelectionSetDiff_of_not_equalUpToReordering
        hleftFree hrightFree hleftNormal hrightNormal hequal
    rcases
        GroundTypeNormalization.normalSelectionSetDiffObservableTrace_of_valid_normal_diff
          hleftValid hrightValid hleftNormal hrightNormal hdiff with
      ⟨responsePath, htrace⟩
    have hnotData :
        ¬ GroundTypeNormalization.selectionSetsDataEquivalent schema
          parentType left right :=
      GroundTypeNormalization.not_selectionSetsDataEquivalent_of_valid_normal_object_diff_observable_trace_pairedPath
        hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
        hrightNormal hobject htrace
    exact False.elim
      (hnotData
        (GroundTypeNormalization.selectionSetsDataEquivalent_of_selectionSetsSemanticallyEquivalent
          hsem))

end CompleteNormalization

end NormalForm

end GraphQL
