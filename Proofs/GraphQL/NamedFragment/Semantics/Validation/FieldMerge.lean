import Proofs.GraphQL.NamedFragment.Semantics.Validation.Base

/-! Named-fragment validation preservation proofs. -/

namespace GraphQL
namespace NamedFragment
namespace Semantics

namespace FieldMergeInline

def inlineScopedField (field : GraphQL.NamedFragment.Validation.FieldMerge.ScopedField)
    : GraphQL.NamedFragment.Validation.FieldMerge.ScopedField :=
  {
    field with
      selectionSet :=
        Inline.inlineSelectionSet field.availableFragments field.selectionSet
      availableFragments := []
  }

mutual
  theorem collectSelection_inlineSelection_eq_map
      : ∀ (schema : Schema) (fragments : List FragmentDefinition)
            (parentType : Name) (selection : Selection),
          GraphQL.NamedFragment.Validation.FieldMerge.collectSelection schema []
            parentType (Inline.inlineSelection fragments selection)
          = (GraphQL.NamedFragment.Validation.FieldMerge.collectSelection schema
              fragments parentType selection).map
              inlineScopedField
    | schema, fragments, parentType,
        .field responseName fieldName arguments directives selectionSet => by
        simp [Inline.inlineSelection,
          GraphQL.NamedFragment.Validation.FieldMerge.collectSelection]
        cases schema.lookupField parentType fieldName <;> simp [inlineScopedField]
    | schema, fragments, parentType,
        .inlineFragment none directives selectionSet => by
        simp [Inline.inlineSelection,
          GraphQL.NamedFragment.Validation.FieldMerge.collectSelection,
          collectFields_inlineSelectionSet_eq_map schema fragments parentType
            selectionSet]
    | schema, fragments, parentType,
        .inlineFragment (some typeCondition) directives selectionSet => by
        simp [Inline.inlineSelection,
          GraphQL.NamedFragment.Validation.FieldMerge.collectSelection,
          collectFields_inlineSelectionSet_eq_map schema fragments typeCondition
            selectionSet]
    | schema, fragments, parentType,
        .fragmentSpread fragmentName directives => by
        simp [Inline.inlineSelection,
          GraphQL.NamedFragment.Validation.FieldMerge.collectSelection]
        cases hlookup : lookupFragmentAndRestLt? fragmentName fragments with
        | none =>
            simp [GraphQL.NamedFragment.Validation.FieldMerge.collectSelection,
              GraphQL.NamedFragment.Validation.FieldMerge.collectFields]
        | some pair =>
            cases pair with
            | mk fragment remainingFragments =>
                simp [GraphQL.NamedFragment.Validation.FieldMerge.collectSelection,
                  collectFields_inlineSelectionSet_eq_map schema
                    remainingFragments.val fragment.typeCondition
                    fragment.selectionSet]
  termination_by _schema fragments _parentType selection =>
    (fragments.length, sizeOf selection, 0)
  decreasing_by
    all_goals
      try subst fragments
      simp_wf
      try
        first
        | apply Prod.Lex.left
          exact remainingFragments.property
        | apply Prod.Lex.right
          apply Prod.Lex.left
          omega
        | apply Prod.Lex.right
          apply Prod.Lex.right
          omega

  theorem collectFields_inlineSelectionSet_eq_map
      : ∀ (schema : Schema) (fragments : List FragmentDefinition)
            (parentType : Name) (selectionSet : List Selection),
          GraphQL.NamedFragment.Validation.FieldMerge.collectFields schema []
            parentType (Inline.inlineSelectionSet fragments selectionSet)
          = (GraphQL.NamedFragment.Validation.FieldMerge.collectFields schema
              fragments parentType selectionSet).map
              inlineScopedField
    | schema, fragments, parentType, [] => by
        simp [GraphQL.NamedFragment.Validation.FieldMerge.collectFields]
    | schema, fragments, parentType, selection :: rest => by
        simp [Inline.inlineSelectionSet,
          GraphQL.NamedFragment.Validation.FieldMerge.collectFields,
          collectSelection_inlineSelection_eq_map schema fragments parentType
            selection,
          collectFields_inlineSelectionSet_eq_map schema fragments parentType
            rest,
          List.map_append]
  termination_by _schema fragments _parentType selectionSet =>
    (fragments.length, sizeOf selectionSet, 1)
  decreasing_by
    all_goals
      try subst fragments
      simp_wf
      repeat first
        | apply Prod.Lex.left; omega
        | apply Prod.Lex.right
      try omega
end

theorem fieldsInSetCanMerge_inlineSelectionSet_inductive
    {schema : Schema} {fragments : List FragmentDefinition}
    {parentType : Name} {selectionSet : List Selection}
    (hmerge
      : GraphQL.NamedFragment.Validation.FieldMerge.FieldsInSetCanMerge schema
          fragments parentType selectionSet)
    : GraphQL.NamedFragment.Validation.FieldMerge.FieldsInSetCanMerge schema []
        parentType (Inline.inlineSelectionSet fragments selectionSet) := by
  refine GraphQL.NamedFragment.Validation.FieldMerge.FieldsInSetCanMerge.rec
    (motive_1 := fun parentType selectionSet _ =>
      GraphQL.NamedFragment.Validation.FieldMerge.FieldsInSetCanMerge schema []
        parentType (Inline.inlineSelectionSet fragments selectionSet))
    (motive_2 := fun left right _ =>
      GraphQL.NamedFragment.Validation.FieldMerge.FieldsForNameCanMerge schema []
        (inlineScopedField left) (inlineScopedField right))
    ?setCase ?fieldCase hmerge
  · intro parentType selectionSet hfields ihFields
    refine GraphQL.NamedFragment.Validation.FieldMerge.FieldsInSetCanMerge.intro
      parentType (Inline.inlineSelectionSet fragments selectionSet) ?_
    dsimp
    intro left hleft right hright hresponse
    rw [collectFields_inlineSelectionSet_eq_map schema fragments parentType
      selectionSet] at hleft hright
    rcases List.mem_map.mp hleft with
      ⟨sourceLeft, hsourceLeft, hsourceLeftEq⟩
    rcases List.mem_map.mp hright with
      ⟨sourceRight, hsourceRight, hsourceRightEq⟩
    cases hsourceLeftEq
    cases hsourceRightEq
    exact ihFields sourceLeft hsourceLeft sourceRight hsourceRight
      (by simpa [inlineScopedField] using hresponse)
  · intro left right hshape hidentity hsubfields ihSubfields
    refine GraphQL.NamedFragment.Validation.FieldMerge.FieldsForNameCanMerge.intro
      (inlineScopedField left) (inlineScopedField right) ?_ ?_ ?_
    · simpa [inlineScopedField,
        GraphQL.FieldMerge.sameResponseShape] using
        hshape
    · intro hparents
      simpa [inlineScopedField] using hidentity hparents
    · intro hparents objectType
      dsimp
      intro subLeft hsubLeft subRight hsubRight hresponse
      simp [inlineScopedField] at hparents
      change subLeft ∈
          GraphQL.NamedFragment.Validation.FieldMerge.collectFields schema []
              objectType
              (Inline.inlineSelectionSet left.availableFragments
                left.selectionSet)
            ++
            GraphQL.NamedFragment.Validation.FieldMerge.collectFields schema []
              objectType
              (Inline.inlineSelectionSet right.availableFragments
                right.selectionSet) at hsubLeft
      change subRight ∈
          GraphQL.NamedFragment.Validation.FieldMerge.collectFields schema []
              objectType
              (Inline.inlineSelectionSet left.availableFragments
                left.selectionSet)
            ++
            GraphQL.NamedFragment.Validation.FieldMerge.collectFields schema []
              objectType
              (Inline.inlineSelectionSet right.availableFragments
                right.selectionSet) at hsubRight
      have hcollect :
          GraphQL.NamedFragment.Validation.FieldMerge.collectFields schema []
                objectType
                (Inline.inlineSelectionSet left.availableFragments
                  left.selectionSet)
              ++
              GraphQL.NamedFragment.Validation.FieldMerge.collectFields schema []
                objectType
                (Inline.inlineSelectionSet right.availableFragments
                  right.selectionSet)
            =
          (GraphQL.NamedFragment.Validation.FieldMerge.collectFields schema
                left.availableFragments objectType left.selectionSet
              ++
              GraphQL.NamedFragment.Validation.FieldMerge.collectFields schema
                right.availableFragments objectType right.selectionSet).map
              inlineScopedField := by
        simp [List.map_append,
          collectFields_inlineSelectionSet_eq_map schema left.availableFragments
            objectType left.selectionSet,
          collectFields_inlineSelectionSet_eq_map schema right.availableFragments
            objectType right.selectionSet]
      rw [hcollect] at hsubLeft hsubRight
      rcases List.mem_map.mp hsubLeft with
        ⟨sourceLeft, hsourceLeft, hsourceLeftEq⟩
      rcases List.mem_map.mp hsubRight with
        ⟨sourceRight, hsourceRight, hsourceRightEq⟩
      cases hsourceLeftEq
      cases hsourceRightEq
      exact ihSubfields hparents objectType sourceLeft hsourceLeft
        sourceRight hsourceRight
        (by simpa [inlineScopedField] using hresponse)

theorem fieldsInSetCanMerge_inlineSelectionSet
    {schema : Schema} {fragments : List FragmentDefinition}
    {parentType : Name} {selectionSet : List Selection}
    (hmerge
      : GraphQL.NamedFragment.Validation.FieldMerge.fieldsInSetCanMerge schema
          fragments parentType selectionSet)
    : GraphQL.NamedFragment.Validation.FieldMerge.fieldsInSetCanMerge schema []
        parentType (Inline.inlineSelectionSet fragments selectionSet) := by
  exact fieldsInSetCanMerge_inlineSelectionSet_inductive hmerge

end FieldMergeInline

theorem inlineOperation_fieldMerge_of_valid
    {schema : Schema} {operation : Operation}
    (hvalid : GraphQL.NamedFragment.Validation.operationDefinitionValid schema operation)
    : GraphQL.NamedFragment.Validation.FieldMerge.fieldsInSetCanMerge schema
        (Inline.inlineOperation operation).fragmentDefinitions
        (Inline.inlineOperation operation).rootType
        (Inline.inlineOperation operation).selectionSet := by
  rcases hvalid with
    ⟨_hroot, _hrootComposite, _hvariables, _huniqueFragments,
      _hfragmentsAcyclic, _hfragmentDefinitionsValid, _hselectionNonempty,
      _hselectionValid, hmerge, _hvariablesUsed⟩
  cases operation with
  | mk name rootType variableDefinitions fragmentDefinitions selectionSet =>
      simp [Inline.inlineOperation]
      exact FieldMergeInline.fieldsInSetCanMerge_inlineSelectionSet hmerge

theorem inlineOperation_fragmentSideConditions (schema : Schema) (operation : Operation)
    : GraphQL.NamedFragment.Validation.fragmentNamesUnique
        (Inline.inlineOperation operation).fragmentDefinitions
      ∧ GraphQL.NamedFragment.Validation.fragmentsAcyclic
          (Inline.inlineOperation operation).fragmentDefinitions
      ∧ GraphQL.NamedFragment.Validation.allFragmentDefinitionsValid schema
          (Inline.inlineOperation operation).variableDefinitions
          (Inline.inlineOperation operation).fragmentDefinitions := by
  cases operation with
  | mk name rootType variableDefinitions fragmentDefinitions selectionSet =>
      simp [Inline.inlineOperation,
        GraphQL.NamedFragment.Validation.fragmentNamesUnique,
        GraphQL.NamedFragment.Validation.fragmentsAcyclic,
        GraphQL.NamedFragment.Validation.fragmentsAcyclicBool,
        GraphQL.NamedFragment.Validation.allFragmentDefinitionsValid]

theorem inlineOperation_valid_of_selectionSetValid
    {schema : Schema} {operation : Operation}
    (hvalid : GraphQL.NamedFragment.Validation.operationDefinitionValid schema operation)
    (hselectionValid
      : GraphQL.NamedFragment.Validation.selectionSetValid schema
          (Inline.inlineOperation operation).variableDefinitions
          (Inline.inlineOperation operation).fragmentDefinitions
          (Inline.inlineOperation operation).rootType
          (Inline.inlineOperation operation).selectionSet)
    : GraphQL.NamedFragment.Validation.operationDefinitionValid schema
        (Inline.inlineOperation operation) := by
  have hvalidOriginal := hvalid
  rcases hvalid with
    ⟨hroot, hrootComposite, hvariables, _huniqueFragments,
      _hfragmentsAcyclic, _hfragmentDefinitionsValid, _hselectionNonempty,
      _originalSelectionValid, _originalMerge, hvariablesUsed⟩
  rcases inlineOperation_fragmentSideConditions schema operation with
    ⟨hfragmentNamesUnique, hfragmentsAcyclic, hallFragmentDefinitionsValid⟩
  constructor
  · simpa [Inline.inlineOperation] using hroot
  constructor
  · simpa [Inline.inlineOperation] using hrootComposite
  constructor
  · simpa [Inline.inlineOperation] using hvariables
  constructor
  · exact hfragmentNamesUnique
  constructor
  · exact hfragmentsAcyclic
  constructor
  · exact hallFragmentDefinitionsValid
  constructor
  · exact inlineOperation_selectionSet_nonempty_of_valid hvalidOriginal
  constructor
  · exact hselectionValid
  constructor
  · exact inlineOperation_fieldMerge_of_valid hvalidOriginal
  · exact inlineOperation_operationVariablesUsed hvariablesUsed

end Semantics
end NamedFragment
end GraphQL
