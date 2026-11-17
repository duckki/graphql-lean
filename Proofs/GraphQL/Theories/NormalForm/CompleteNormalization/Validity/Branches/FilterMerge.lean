import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.FilterMerge

/-! Boolean filtering preserves the declared-scope merge checks used by validity. -/

namespace GraphQL.NormalForm.CompleteNormalization

theorem fieldsInSetCanMerge_filterSelectionSetBoolCase
    (schema : Schema) (boolCase : BoolCase)
    {parentType : Name} {selectionSet : List Selection}
    : FieldMerge.fieldsInSetCanMerge schema parentType selectionSet
      -> FieldMerge.fieldsInSetCanMerge schema parentType
          (filterSelectionSetBoolCase boolCase selectionSet) :=
  fieldsInSetCanMerge_filterSelectionSetBoolCase_forSemantics schema boolCase

theorem fieldsInSetCanMerge_filterSelectionSetBoolCase_pair
    (schema : Schema)
    {parentType : Name} {leftSet rightSet : List Selection}
    (leftCase rightCase : BoolCase)
    : FieldMerge.fieldsInSetCanMerge schema parentType (leftSet ++ rightSet)
      -> FieldMerge.fieldsInSetCanMerge schema parentType
          (filterSelectionSetBoolCase leftCase leftSet
            ++ filterSelectionSetBoolCase rightCase rightSet) := by
  intro hmerge
  refine FieldMerge.fieldsInSetCanMerge_transport
    (fun source target =>
      ∃ boolCase, BoolFilteredScopedFieldSourceForMerge schema boolCase source target)
    ?_ ?_ hmerge parentType
    (filterSelectionSetBoolCase leftCase leftSet
      ++ filterSelectionSetBoolCase rightCase rightSet) ?_
  · intro source target hsource
    rcases hsource with ⟨boolCase, hsource⟩
    exact ⟨hsource.parentType, hsource.responseName, hsource.fieldName,
      hsource.arguments, hsource.outputType⟩
  · intro sourceLeft sourceRight targetLeft targetRight hleft hright field hfield
    rcases hleft with ⟨leftCase, hleft⟩
    rcases hright with ⟨rightCase, hright⟩
    simp only [FieldMerge.collectSubfields, List.mem_append] at hfield
    rcases hfield with hfield | hfield
    · rw [hleft.outputType, hleft.selectionSet] at hfield
      rcases collectFields_filterSelectionSetBoolCase_mem_source_forMerge schema leftCase
          sourceLeft.outputType.namedType sourceLeft.selectionSet field hfield with
        ⟨sourceField, hsourceField, hsource⟩
      exact ⟨sourceField, List.mem_append_left _ hsourceField, leftCase, hsource⟩
    · rw [hright.outputType, hright.selectionSet] at hfield
      rcases collectFields_filterSelectionSetBoolCase_mem_source_forMerge schema rightCase
          sourceRight.outputType.namedType sourceRight.selectionSet field hfield with
        ⟨sourceField, hsourceField, hsource⟩
      exact ⟨sourceField, List.mem_append_right _ hsourceField, rightCase, hsource⟩
  · intro field hfield
    rw [FieldMerge.collectFields_append] at hfield
    rcases List.mem_append.mp hfield with hfield | hfield
    · rcases collectFields_filterSelectionSetBoolCase_mem_source_forMerge schema leftCase
          parentType leftSet field hfield with
        ⟨sourceField, hsourceField, hsource⟩
      refine ⟨sourceField, ?_, leftCase, hsource⟩
      rw [FieldMerge.collectFields_append]
      exact List.mem_append_left _ hsourceField
    · rcases collectFields_filterSelectionSetBoolCase_mem_source_forMerge schema rightCase
          parentType rightSet field hfield with
        ⟨sourceField, hsourceField, hsource⟩
      refine ⟨sourceField, ?_, rightCase, hsource⟩
      rw [FieldMerge.collectFields_append]
      exact List.mem_append_right _ hsourceField

end GraphQL.NormalForm.CompleteNormalization
