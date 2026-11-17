import GraphQL.Validation

/-! Wrapper and leaf-type compatibility facts used by field-merge validation. -/

namespace GraphQL.FieldMerge

theorem sameTypeShape_refl (schema : Schema)
    : ∀ typeRef, typeRef.isOutputType schema -> sameTypeShape schema typeRef typeRef
  | .named _typeName, houtput => by
      exact ⟨houtput, houtput, by intro _hleaf; rfl⟩
  | .list inner, houtput => by
      exact sameTypeShape_refl schema inner
        (by simpa [TypeRef.isOutputType] using houtput)
  | .nonNull inner, houtput => by
      have hinner : inner.isOutputType schema := by
        cases inner with
        | named _typeName =>
            exact houtput
        | list _inner =>
            exact houtput
        | nonNull _inner =>
            simp [TypeRef.isOutputType] at houtput
      exact sameTypeShape_refl schema inner hinner

theorem sameTypeShape_symm (schema : Schema)
    : ∀ left right, sameTypeShape schema left right -> sameTypeShape schema right left
  | .named _left, .named _right, hshape => by
      exact ⟨hshape.2.1, hshape.1,
        by
          intro hleaf
          exact (hshape.2.2
            (Or.elim hleaf (fun hright => Or.inr hright)
              (fun hleft => Or.inl hleft))).symm⟩
  | .list left, .list right, hshape => by
      exact sameTypeShape_symm schema left right hshape
  | .nonNull left, .nonNull right, hshape => by
      exact sameTypeShape_symm schema left right hshape
  | .named _, .list _, hshape => by
      simp [sameTypeShape] at hshape
  | .named _, .nonNull _, hshape => by
      simp [sameTypeShape] at hshape
  | .list _, .named _, hshape => by
      simp [sameTypeShape] at hshape
  | .list _, .nonNull _, hshape => by
      simp [sameTypeShape] at hshape
  | .nonNull _, .named _, hshape => by
      simp [sameTypeShape] at hshape
  | .nonNull _, .list _, hshape => by
      simp [sameTypeShape] at hshape

theorem sameTypeShape_trans (schema : Schema)
    : ∀ left middle right,
        sameTypeShape schema left middle
        -> sameTypeShape schema middle right
        -> sameTypeShape schema left right
  | .named left, .named middle, .named right, hleft, hright => by
      exact ⟨hleft.1, hright.2.1,
        by
          intro hleaf
          rcases hleaf with hleftLeaf | hrightLeaf
          · have hleftMiddle : left = middle :=
              hleft.2.2 (Or.inl hleftLeaf)
            have hmiddleLeaf : schema.isLeafType middle := by
              simpa [hleftMiddle] using hleftLeaf
            have hmiddleRight : middle = right :=
              hright.2.2 (Or.inl hmiddleLeaf)
            exact hleftMiddle.trans hmiddleRight
          · have hmiddleRight : middle = right :=
              hright.2.2 (Or.inr hrightLeaf)
            have hmiddleLeaf : schema.isLeafType middle := by
              simpa [hmiddleRight] using hrightLeaf
            have hleftMiddle : left = middle :=
              hleft.2.2 (Or.inr hmiddleLeaf)
            exact hleftMiddle.trans hmiddleRight⟩
  | .list left, .list middle, .list right, hleft, hright => by
      exact sameTypeShape_trans schema left middle right hleft hright
  | .nonNull left, .nonNull middle, .nonNull right, hleft, hright => by
      exact sameTypeShape_trans schema left middle right hleft hright
  | .named _, .named _, .list _, _hleft, hright => by
      simp [sameTypeShape] at hright
  | .named _, .named _, .nonNull _, _hleft, hright => by
      simp [sameTypeShape] at hright
  | .named _, .list _, _, hleft, _hright => by
      simp [sameTypeShape] at hleft
  | .named _, .nonNull _, _, hleft, _hright => by
      simp [sameTypeShape] at hleft
  | .list _, .named _, _, hleft, _hright => by
      simp [sameTypeShape] at hleft
  | .list _, .list _, .named _, _hleft, hright => by
      simp [sameTypeShape] at hright
  | .list _, .list _, .nonNull _, _hleft, hright => by
      simp [sameTypeShape] at hright
  | .list _, .nonNull _, _, hleft, _hright => by
      simp [sameTypeShape] at hleft
  | .nonNull _, .named _, _, hleft, _hright => by
      simp [sameTypeShape] at hleft
  | .nonNull _, .list _, _, hleft, _hright => by
      simp [sameTypeShape] at hleft
  | .nonNull _, .nonNull _, .named _, _hleft, hright => by
      simp [sameTypeShape] at hright
  | .nonNull _, .nonNull _, .list _, _hleft, hright => by
      simp [sameTypeShape] at hright

theorem sameTypeShape_namedType (schema : Schema)
    : ∀ left right,
        sameTypeShape schema left right
        -> sameTypeShape schema (.named left.namedType) (.named right.namedType)
  | .named _, .named _, hshape => hshape
  | .list left, .list right, hshape => sameTypeShape_namedType schema left right hshape
  | .nonNull left, .nonNull right, hshape => sameTypeShape_namedType schema left right hshape
  | .named _, .list _, hshape => by simp [sameTypeShape] at hshape
  | .named _, .nonNull _, hshape => by simp [sameTypeShape] at hshape
  | .list _, .named _, hshape => by simp [sameTypeShape] at hshape
  | .list _, .nonNull _, hshape => by simp [sameTypeShape] at hshape
  | .nonNull _, .named _, hshape => by simp [sameTypeShape] at hshape
  | .nonNull _, .list _, hshape => by simp [sameTypeShape] at hshape

theorem sameTypeShape_composite_left (schema : Schema)
    {left right : TypeRef} (hshape : sameTypeShape schema left right)
    (hright : schema.isCompositeType right.namedType)
    : schema.isCompositeType left.namedType := by
  have hnamed := sameTypeShape_namedType schema left right hshape
  by_cases hleaf : schema.isLeafType left.namedType
  · have heq := hnamed.2.2 (Or.inl hleaf)
    simpa [heq] using hright
  · rcases hnamed.1 with ⟨definition, hlookup, houtput⟩
    have hnotLeaf : ¬ definition.isLeafType := fun h => hleaf ⟨definition, hlookup, h⟩
    refine ⟨definition, hlookup, ?_⟩
    cases definition <;>
      simp_all [TypeDefinition.isOutputType, TypeDefinition.isLeafType,
        TypeDefinition.isCompositeType]

end GraphQL.FieldMerge
