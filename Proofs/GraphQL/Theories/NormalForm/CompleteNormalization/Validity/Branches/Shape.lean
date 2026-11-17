import Proofs.GraphQL.Validation.FieldMerge

/-! Construct recursive response shapes from mergeability at the declared return type. -/

namespace GraphQL.NormalForm.CompleteNormalization

theorem fieldsForNameCanMerge_of_sameOutput_subfields
    {schema : Schema} {left right : FieldMerge.ScopedField}
    (houtput : left.outputType = right.outputType)
    (htypes : FieldMerge.sameTypeShape schema left.outputType right.outputType)
    (hidentity
      : (left.parentType = right.parentType
          ∨ ¬ schema.objectType left.parentType
          ∨ ¬ schema.objectType right.parentType)
        -> left.fieldName = right.fieldName
            ∧ Argument.argumentsEquivalent left.arguments right.arguments)
    (hsubfields
      : FieldMerge.fieldsInSetCanMerge schema left.outputType.namedType
          (left.selectionSet ++ right.selectionSet))
    : FieldMerge.fieldsForNameCanMerge schema left right := by
  have hchildren :
      ∀ childLeft, childLeft ∈ FieldMerge.collectSubfields schema left right
        -> ∀ childRight, childRight ∈ FieldMerge.collectSubfields schema left right
        -> childLeft.responseName = childRight.responseName
        -> FieldMerge.fieldsForNameCanMerge schema childLeft childRight := by
    intro childLeft hleft childRight hright hresponse
    apply FieldMerge.fieldsInSetCanMerge_pair hsubfields
    · simpa only [FieldMerge.collectSubfields, ← houtput,
        FieldMerge.collectFields_append] using hleft
    · simpa only [FieldMerge.collectSubfields, ← houtput,
        FieldMerge.collectFields_append] using hright
    · exact hresponse
  refine .intro left right (.intro left right htypes ?_) hidentity ?_
  · intro _hleftComposite _hrightComposite childLeft hleft childRight hright hresponse
    exact FieldMerge.fieldsForNameCanMerge_sameResponseShape
      (hchildren childLeft hleft childRight hright hresponse)
  · intro _hparents
    exact hchildren

end GraphQL.NormalForm.CompleteNormalization
