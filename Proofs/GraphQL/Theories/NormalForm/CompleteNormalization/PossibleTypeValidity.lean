import Proofs.GraphQL.Theories.NormalForm.Shared.PossibleTypeValidity

/-! Complete normality and ordinary validity imply possible-type field validity. -/

namespace GraphQL.NormalForm.CompleteNormalization

theorem completeNormalBooleanStem_validInPossibleTypes
    {schema : Schema} {definitions : List VariableDefinition} {parentType : Name}
    (hparent : schema.objectType parentType)
    : ∀ {boolCase : BoolCase} {selection : Selection} {body : List Selection},
        completeNormalBooleanStem boolCase selection body
        -> Validation.selectionValid schema definitions parentType selection
        -> selectionSetGroundTyped schema parentType body
        -> selectionValidInPossibleTypes schema definitions parentType selection
  | [], _, _, hstem, _, _ => by
      simp [completeNormalBooleanStem] at hstem
  | [(_, _)], .inlineFragment none [_] children, body, hstem, hvalid, hground => by
      obtain ⟨_, rfl⟩ := hstem
      intro objectType hpossible
      exact selectionSetValidInPossibleTypes_of_groundTyped hground
        (Validation.selectionValid_inlineFragment_none_selectionSetValid hvalid) hpossible
  | (_, _) :: (_, _) :: _, .inlineFragment none [_] [child], body,
      hstem, hvalid, hground => by
      have hchildValid :=
        Validation.selectionValid_inlineFragment_none_selectionSetValid hvalid
      unfold Validation.selectionSetValid at hchildValid
      intro objectType hpossible
      have heq : objectType = parentType :=
        object_typeIncludesObjectBool_eq_self schema hparent
          (by simpa [Schema.typeIncludesObjectBool] using hpossible)
      subst objectType
      exact ⟨completeNormalBooleanStem_validInPossibleTypes hparent hstem.2
        (hchildValid child (by simp)) hground, trivial⟩
  | _ :: _ :: _, .field _ _ _ _ _, _, hstem, _, _ => by
      simp [completeNormalBooleanStem] at hstem
  | _ :: _ :: _, .inlineFragment none [] _, _, hstem, _, _ => by
      simp [completeNormalBooleanStem] at hstem
  | _ :: _ :: _, .inlineFragment none (_ :: _ :: _) _, _, hstem, _, _ => by
      simp [completeNormalBooleanStem] at hstem
  | _ :: _ :: _, .inlineFragment (some _) _ _, _, hstem, _, _ => by
      simp [completeNormalBooleanStem] at hstem
  | [_], .field _ _ _ _ _, _, hstem, _, _ => by
      simp [completeNormalBooleanStem] at hstem
  | [_], .inlineFragment none [] _, _, hstem, _, _ => by
      simp [completeNormalBooleanStem] at hstem
  | [_], .inlineFragment none (_ :: _ :: _) _, _, hstem, _, _ => by
      simp [completeNormalBooleanStem] at hstem
  | [_], .inlineFragment (some _) _ _, _, hstem, _, _ => by
      simp [completeNormalBooleanStem] at hstem

theorem completeNormalSelectionSet_validInPossibleTypes
    {schema : Schema} {definitions : List VariableDefinition}
    {variables : List BoolVar} {parentType : Name} {selections : List Selection}
    (hparent : schema.objectType parentType)
    (hnormal : completeNormalSelectionSet schema variables parentType selections)
    (hvalid : Validation.selectionSetValid schema definitions parentType selections)
    : selectionSetValidInPossibleTypes schema definitions parentType selections := by
  cases variables with
  | nil =>
      exact selectionSetValidInPossibleTypes_of_groundTyped hnormal.2.1.1 hvalid
        (by
          simpa [Schema.typeIncludesObjectBool]
            using object_typeIncludesObjectBool_self schema hparent)
  | cons varName variables =>
      have hbranches := hnormal.2.2.1
      clear hnormal
      induction selections with
      | nil => trivial
      | cons selection rest ih =>
          obtain ⟨boolCase, body, _, hstem, hbodyNormal, _⟩ :=
            hbranches selection (by simp)
          unfold Validation.selectionSetValid at hvalid
          refine ⟨
            completeNormalBooleanStem_validInPossibleTypes hparent hstem
              (hvalid selection (by simp)) hbodyNormal.1,
            ?_
          ⟩
          apply ih
          · unfold Validation.selectionSetValid
            exact fun child hmem => hvalid child (by simp [hmem])
          · exact fun child hmem => hbranches child (by simp [hmem])

theorem operationFieldsValidInPossibleTypes_of_completeNormal
    {schema : Schema} {operation : Operation}
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hvalid : Validation.operationDefinitionValid schema operation)
    (hnormal : completeNormalOperation schema operation)
    : operationFieldsValidInPossibleTypes schema operation := by
  have hroot : schema.objectType (operation.rootType schema) := by
    cases operation.operationType
    exact hschema.2.1
  exact completeNormalSelectionSet_validInPossibleTypes hroot hnormal
    (Validation.operationDefinitionValid_selectionSetValid hvalid)

end GraphQL.NormalForm.CompleteNormalization
