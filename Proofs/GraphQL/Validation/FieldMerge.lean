import GraphQL.Validation
import Proofs.GraphQL.Argument

/-!
Facts for same-response-name field merge validation.
-/

namespace GraphQL

namespace FieldMerge

theorem sameResponseShape_refl (schema : Schema)
    : ∀ typeRef, typeRef.isOutputType schema -> sameResponseShape schema typeRef typeRef
  | .named _typeName, houtput => by
      exact ⟨houtput, houtput, by intro _hleaf; rfl⟩
  | .list inner, houtput => by
      exact sameResponseShape_refl schema inner
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
      exact sameResponseShape_refl schema inner hinner

theorem sameResponseShape_symm (schema : Schema)
    : ∀ left right,
        sameResponseShape schema left right -> sameResponseShape schema right left
  | .named _left, .named _right, hshape => by
      exact ⟨hshape.2.1, hshape.1,
        by
          intro hleaf
          exact (hshape.2.2
            (Or.elim hleaf (fun hright => Or.inr hright)
              (fun hleft => Or.inl hleft))).symm⟩
  | .list left, .list right, hshape => by
      exact sameResponseShape_symm schema left right hshape
  | .nonNull left, .nonNull right, hshape => by
      exact sameResponseShape_symm schema left right hshape
  | .named _, .list _, hshape => by
      simp [sameResponseShape] at hshape
  | .named _, .nonNull _, hshape => by
      simp [sameResponseShape] at hshape
  | .list _, .named _, hshape => by
      simp [sameResponseShape] at hshape
  | .list _, .nonNull _, hshape => by
      simp [sameResponseShape] at hshape
  | .nonNull _, .named _, hshape => by
      simp [sameResponseShape] at hshape
  | .nonNull _, .list _, hshape => by
      simp [sameResponseShape] at hshape

theorem sameResponseShape_trans (schema : Schema)
    : ∀ left middle right,
        sameResponseShape schema left middle
        -> sameResponseShape schema middle right
        -> sameResponseShape schema left right
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
      exact sameResponseShape_trans schema left middle right hleft hright
  | .nonNull left, .nonNull middle, .nonNull right, hleft, hright => by
      exact sameResponseShape_trans schema left middle right hleft hright
  | .named _, .named _, .list _, _hleft, hright => by
      simp [sameResponseShape] at hright
  | .named _, .named _, .nonNull _, _hleft, hright => by
      simp [sameResponseShape] at hright
  | .named _, .list _, _, hleft, _hright => by
      simp [sameResponseShape] at hleft
  | .named _, .nonNull _, _, hleft, _hright => by
      simp [sameResponseShape] at hleft
  | .list _, .named _, _, hleft, _hright => by
      simp [sameResponseShape] at hleft
  | .list _, .list _, .named _, _hleft, hright => by
      simp [sameResponseShape] at hright
  | .list _, .list _, .nonNull _, _hleft, hright => by
      simp [sameResponseShape] at hright
  | .list _, .nonNull _, _, hleft, _hright => by
      simp [sameResponseShape] at hleft
  | .nonNull _, .named _, _, hleft, _hright => by
      simp [sameResponseShape] at hleft
  | .nonNull _, .list _, _, hleft, _hright => by
      simp [sameResponseShape] at hleft
  | .nonNull _, .nonNull _, .named _, _hleft, hright => by
      simp [sameResponseShape] at hright
  | .nonNull _, .nonNull _, .list _, _hleft, hright => by
      simp [sameResponseShape] at hright

theorem fieldsInSetCanMerge_pair
    {schema : Schema} {parentType : Name} {selectionSet : List Selection}
    {left right : ScopedField}
    : fieldsInSetCanMerge schema parentType selectionSet
      -> left ∈ collectFields schema parentType selectionSet
      -> right ∈ collectFields schema parentType selectionSet
      -> left.responseName = right.responseName
      -> fieldsForNameCanMerge schema left right := by
  intro hmerge hleft hright hresponse
  unfold fieldsInSetCanMerge at hmerge
  cases hmerge with
  | intro _ _ hfields =>
      exact hfields left hleft right hright hresponse

theorem fieldsForNameCanMerge_sameResponseShape
    {schema : Schema} {left right : ScopedField}
    : fieldsForNameCanMerge schema left right
      -> sameResponseShape schema left.outputType right.outputType := by
  intro hmerge
  unfold fieldsForNameCanMerge at hmerge
  cases hmerge with
  | intro _ _ hshape _hidentity _hsubfields =>
      exact hshape

theorem fieldsForNameCanMerge_identity {schema : Schema} {left right : ScopedField}
    : fieldsForNameCanMerge schema left right
      -> (left.parentType = right.parentType
          ∨ ¬ schema.objectType left.parentType
          ∨ ¬ schema.objectType right.parentType)
      -> left.fieldName = right.fieldName
          ∧ Argument.argumentsEquivalent left.arguments right.arguments := by
  intro hmerge hparents
  unfold fieldsForNameCanMerge at hmerge
  cases hmerge with
  | intro _ _ _hshape hidentity _hsubfields =>
      exact hidentity hparents

theorem fieldsForNameCanMerge_same_parent_identity
    {schema : Schema} {left right : ScopedField}
    : fieldsForNameCanMerge schema left right
      -> left.parentType = right.parentType
      -> left.fieldName = right.fieldName
          ∧ Argument.argumentsEquivalent left.arguments right.arguments := by
  intro hmerge hparent
  exact fieldsForNameCanMerge_identity hmerge (Or.inl hparent)

theorem fieldsForNameCanMerge_subfields {schema : Schema} {left right : ScopedField}
    : fieldsForNameCanMerge schema left right
      -> (left.parentType = right.parentType
          ∨ ¬ schema.objectType left.parentType
          ∨ ¬ schema.objectType right.parentType)
      -> ∀ objectType,
          fieldsInSetCanMerge schema objectType
            (left.selectionSet ++ right.selectionSet) := by
  intro hmerge hparents objectType
  unfold fieldsForNameCanMerge at hmerge
  cases hmerge with
  | intro _ _ _hshape _hidentity hsubfields =>
      exact hsubfields hparents objectType

theorem collectFields_append (schema : Schema) (parentType : Name)
    : ∀ left right,
        collectFields schema parentType (left ++ right)
        = collectFields schema parentType left ++ collectFields schema parentType right
  | [], _right => by
      simp [collectFields]
  | selection :: rest, right => by
      cases selection with
      | field responseName fieldName arguments directives selectionSet =>
          cases hlookup : schema.lookupField parentType fieldName with
          | none =>
              simp [collectFields, hlookup,
                collectFields_append schema parentType rest right]
          | some fieldDefinition =>
              simp [collectFields, hlookup,
                collectFields_append schema parentType rest right]
      | inlineFragment typeCondition directives selectionSet =>
          cases typeCondition with
          | none =>
              simp [collectFields,
                collectFields_append schema parentType rest right,
                List.append_assoc]
          | some typeCondition =>
              simp [collectFields,
                collectFields_append schema parentType rest right,
                List.append_assoc]

theorem inputValue_structuralEquivalent_symm
    : ∀ left right,
        InputValue.structuralEquivalent left right
        -> InputValue.structuralEquivalent right left :=
  fun _left _right h => InputValue.structuralEquivalent_symm h

theorem inputValue_structuralValuesEquivalent_symm
    : ∀ left right,
        InputValue.structuralValuesEquivalent left right
        -> InputValue.structuralValuesEquivalent right left :=
  fun _left _right h => InputValue.structuralValuesEquivalent_symm h

theorem inputValue_structuralObjectFieldsEquivalent_symm
    : ∀ left right,
        InputValue.structuralObjectFieldsEquivalent left right
        -> InputValue.structuralObjectFieldsEquivalent right left :=
  fun _left _right h => InputValue.structuralObjectFieldsEquivalent_symm h

theorem inputValue_equivalent_symm {left right : InputValue}
    : left.equivalent right -> right.equivalent left :=
  InputValue.equivalent_symm

theorem argumentEquivalent_symm {left right : Argument}
    : left.equivalent right -> right.equivalent left :=
  Argument.equivalent_symm

theorem argumentsEquivalent_symm {left right : List Argument}
    : Argument.argumentsEquivalent left right
      -> Argument.argumentsEquivalent right left :=
  Argument.argumentsEquivalent_symm

theorem fieldsInSetCanMerge_append_comm
    {schema : Schema} {parentType : Name} {left right : List Selection}
    : fieldsInSetCanMerge schema parentType (left ++ right)
      -> fieldsInSetCanMerge schema parentType (right ++ left) := by
  intro hmerge
  unfold fieldsInSetCanMerge
  refine FieldsInSetCanMerge.intro parentType (right ++ left) ?_
  dsimp
  intro sourceLeft hleft sourceRight hright hresponse
  rw [collectFields_append] at hleft hright
  rcases List.mem_append.mp hleft with hleftRight | hleftLeft
  · rcases List.mem_append.mp hright with hrightRight | hrightLeft
    · exact fieldsInSetCanMerge_pair hmerge
        (by
          rw [collectFields_append]
          exact List.mem_append_right
            (collectFields schema parentType left) hleftRight)
        (by
          rw [collectFields_append]
          exact List.mem_append_right
            (collectFields schema parentType left) hrightRight)
        hresponse
    · exact fieldsInSetCanMerge_pair hmerge
        (by
          rw [collectFields_append]
          exact List.mem_append_right
            (collectFields schema parentType left) hleftRight)
        (by
          rw [collectFields_append]
          exact List.mem_append_left
            (collectFields schema parentType right) hrightLeft)
        hresponse
  · rcases List.mem_append.mp hright with hrightRight | hrightLeft
    · exact fieldsInSetCanMerge_pair hmerge
        (by
          rw [collectFields_append]
          exact List.mem_append_left
            (collectFields schema parentType right) hleftLeft)
        (by
          rw [collectFields_append]
          exact List.mem_append_right
            (collectFields schema parentType left) hrightRight)
        hresponse
    · exact fieldsInSetCanMerge_pair hmerge
        (by
          rw [collectFields_append]
          exact List.mem_append_left
            (collectFields schema parentType right) hleftLeft)
        (by
          rw [collectFields_append]
          exact List.mem_append_left
            (collectFields schema parentType right) hrightLeft)
        hresponse

theorem fieldsForNameCanMerge_symm {schema : Schema} {left right : ScopedField}
    : fieldsForNameCanMerge schema left right
      -> fieldsForNameCanMerge schema right left := by
  intro hmerge
  unfold fieldsForNameCanMerge at hmerge ⊢
  cases hmerge with
  | intro _ _ hshape hidentity hsubfields =>
      refine FieldsForNameCanMerge.intro right left ?_ ?_ ?_
      · exact sameResponseShape_symm schema left.outputType right.outputType
          hshape
      · intro hparents
        have hsourceParents :
            left.parentType = right.parentType
              ∨ ¬ schema.objectType left.parentType
              ∨ ¬ schema.objectType right.parentType := by
          rcases hparents with hparentEq | hnotObject
          · exact Or.inl hparentEq.symm
          · rcases hnotObject with hrightNotObject | hleftNotObject
            · exact Or.inr (Or.inr hrightNotObject)
            · exact Or.inr (Or.inl hleftNotObject)
        rcases hidentity hsourceParents with ⟨hfieldName, harguments⟩
        exact ⟨hfieldName.symm, argumentsEquivalent_symm harguments⟩
      · intro hparents objectType
        have hsourceParents :
            left.parentType = right.parentType
              ∨ ¬ schema.objectType left.parentType
              ∨ ¬ schema.objectType right.parentType := by
          rcases hparents with hparentEq | hnotObject
          · exact Or.inl hparentEq.symm
          · rcases hnotObject with hrightNotObject | hleftNotObject
            · exact Or.inr (Or.inr hrightNotObject)
            · exact Or.inr (Or.inl hleftNotObject)
        exact fieldsInSetCanMerge_append_comm
          (hsubfields hsourceParents objectType)

end FieldMerge

end GraphQL
