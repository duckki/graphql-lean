import GraphQL.Theories.QueryInclusion

/-! Supporting lemmas extracted from commit `7797374fd` for the talk exercises. -/

namespace GraphQL.FieldMerge

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

end GraphQL.FieldMerge
