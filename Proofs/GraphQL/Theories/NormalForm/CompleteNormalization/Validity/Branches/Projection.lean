import Proofs.GraphQL.Theories.NormalForm.Shared.FieldProjection
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.FieldProjection
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.ScopedSelections.Basics

/-! Assemble a validity merge check from recursively projected static source groups. -/

namespace GraphQL.NormalForm.CompleteNormalization

theorem fieldsInSetCanMerge_of_fieldProjectionSources_forValidity
    {schema : Schema} {sourceParent targetParent : Name}
    {sourceSet targetSet : List Selection}
    (hmerge : FieldMerge.fieldsInSetCanMerge schema sourceParent sourceSet)
    (hprojection
      : ∀ target,
          target ∈ FieldMerge.collectFields schema targetParent targetSet
          -> ∃ sources,
              sources ⊆ FieldMerge.collectFields schema sourceParent sourceSet
              ∧ FieldProjection schema sources target)
    : FieldMerge.fieldsInSetCanMerge schema targetParent targetSet := by
  refine .intro targetParent targetSet ?_
  dsimp
  intro left hleft right hright hresponse
  rcases hprojection left hleft with ⟨leftSources, hleftSubset, hleftProjection⟩
  rcases hprojection right hright with ⟨rightSources, hrightSubset, hrightProjection⟩
  apply FieldProjection.canMerge schema left right hleftProjection hrightProjection
    hresponse
  intro sourceLeft hsourceLeft sourceRight hsourceRight hsourceResponse
  have hsubset : leftSources ++ rightSources
      ⊆ FieldMerge.collectFields schema sourceParent sourceSet := by
    intro source hsource
    exact (List.mem_append.mp hsource).elim
      (fun hsource => hleftSubset hsource) (fun hsource => hrightSubset hsource)
  exact FieldMerge.fieldsInSetCanMerge_pair hmerge
    (hsubset hsourceLeft) (hsubset hsourceRight) hsourceResponse

theorem normalizeSelectionSets_fieldsInSetCanMerge_of_declaredSources
    (schema : Schema) (hschema : SchemaWellFormedness.schemaWellFormed schema)
    {parentType : Name} {leftSet rightSet : List Selection}
    (hleftShapes : selectionSetFieldsSameOutputShape schema leftSet)
    (hrightShapes : selectionSetFieldsSameOutputShape schema rightSet)
    (hobject : schema.objectType parentType)
    (hleftFree : selectionSetDirectiveFree leftSet)
    (hrightFree : selectionSetDirectiveFree rightSet)
    (hleftReady : selectionSetSemanticsReady schema parentType leftSet)
    (hrightReady : selectionSetSemanticsReady schema parentType rightSet)
    (hleftDeclared : selectionSetDeclaredLookupReady schema parentType leftSet)
    (hrightDeclared : selectionSetDeclaredLookupReady schema parentType rightSet)
    (hmerge : FieldMerge.fieldsInSetCanMerge schema parentType (leftSet ++ rightSet))
    : FieldMerge.fieldsInSetCanMerge schema parentType
        (normalizeSelectionSet schema parentType leftSet
          ++ normalizeSelectionSet schema parentType rightSet) := by
  have hsource := runtimeMergeSources_of_declaredLookupReady schema hobject
    (object_typeIncludesObjectBool_self schema hobject)
    (selectionSetDeclaredLookupReady_append hleftDeclared hrightDeclared) hmerge
  have hleftSource := runtimeMergeSources_of_fields_subset hsource
    (target := leftSet) (by
      intro responseName field hfield
      rw [fieldSelectionsWithResponseNameInScope_append]
      exact List.mem_append_left _ hfield)
  have hrightSource := runtimeMergeSources_of_fields_subset hsource
    (target := rightSet) (by
      intro responseName field hfield
      rw [fieldSelectionsWithResponseNameInScope_append]
      exact List.mem_append_right _ hfield)
  apply fieldsInSetCanMerge_of_fieldProjectionSources_forValidity hmerge
  intro target htarget
  rw [FieldMerge.collectFields_append] at htarget
  rcases List.mem_append.mp htarget with htarget | htarget
  · exact GroundTypeNormalization.normalizeSelectionSet_fieldProjection schema hschema
      parentType leftSet _ hleftShapes hobject hleftFree hleftReady hleftSource target htarget
  · exact GroundTypeNormalization.normalizeSelectionSet_fieldProjection schema hschema
      parentType rightSet _ hrightShapes hobject hrightFree hrightReady hrightSource target htarget

end GraphQL.NormalForm.CompleteNormalization
