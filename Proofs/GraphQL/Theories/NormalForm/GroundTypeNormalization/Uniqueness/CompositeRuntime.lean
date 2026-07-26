import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.DataSeparation
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.DeepSuccess
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.DiffObservable
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.RuntimeCoherence

/-!
Composite runtime selection helpers.

These lemmas select the concrete object runtime used when a composite field is
observed by a tagged probe. They are shared by contextual and selected-path
witness constructions.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

theorem fieldHeadCompositeRuntime_framed_members_of_valid_normal_mem
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType responseName fieldName : Name}
    {arguments : List Argument} {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    {members : List (List Selection)}
    {fieldDefinition : FieldDefinition}
    : Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> (∀ memberSelectionSet,
            memberSelectionSet ∈ members
            -> ∃ variableDefinitions,
                Validation.selectionSetValid schema variableDefinitions parentType
                  memberSelectionSet
                ∧ selectionSetDirectiveFree memberSelectionSet
                ∧ selectionSetNormal schema parentType memberSelectionSet)
      -> selectionSet ∈ members
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> ∃ runtimeType,
          (((objectTypeNameBool schema fieldDefinition.outputType.namedType = true
                ∧ runtimeType = fieldDefinition.outputType.namedType)
              ∨ ((TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool
                      schema
                    = true
                  ∧ objectTypeNameBool schema fieldDefinition.outputType.namedType = false
                  ∧ abstractRuntimeForFieldHeadDeep? schema parentType fieldName
                      arguments parentType
                      [Selection.inlineFragment (some parentType) []
                        (List.flatten members)]
                    = some runtimeType))
            ∧ schema.typeIncludesObjectBool
                fieldDefinition.outputType.namedType runtimeType
              = true) := by
  intro hvalid hnormal hmembers hmember hmem hlookup hcomposite
  by_cases hobject :
      objectTypeNameBool schema fieldDefinition.outputType.namedType = true
  · exact
      ⟨fieldDefinition.outputType.namedType,
        Or.inl ⟨hobject, rfl⟩,
        typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject⟩
  · have hnonObject :
        objectTypeNameBool schema fieldDefinition.outputType.namedType =
          false := by
      cases h : objectTypeNameBool schema fieldDefinition.outputType.namedType
      · rfl
      · contradiction
    rcases
        abstractRuntimeForFieldHeadDeep?_some_of_valid_normal_abstract_mem_lookup
          hvalid hnormal hmem hlookup hcomposite hnonObject with
      ⟨localRuntimeType, hlocalRuntime, _hlocalInclude⟩
    rcases
        abstractRuntimeForFieldHeadDeep?_member_framed_promote_some_of_valid_normal_members
          (schema := schema) (currentParent := parentType)
          (targetParent := parentType) (targetField := fieldName)
          (targetArguments := arguments)
          (targetRuntimeType := localRuntimeType)
          (selectionSet := selectionSet) (members := members)
          (targetFieldDefinition := fieldDefinition)
          hmembers hmember hlookup hcomposite hnonObject hlocalRuntime with
      ⟨runtimeType, hframedRuntime, hinclude⟩
    exact
      ⟨runtimeType,
        Or.inr ⟨hcomposite, hnonObject, hframedRuntime⟩, hinclude⟩

theorem fieldHeadCompositeRuntime_of_valid_normal_mem
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {rootSelectionSet : List Selection}
    {parentType responseName fieldName : Name}
    {arguments : List Argument} {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    : Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> selectionSetDeepHeadPromotionAvailable schema rootSelectionSet parentType
          selectionSet
      -> ∃ runtimeType,
          (((objectTypeNameBool schema fieldDefinition.outputType.namedType = true
                ∧ runtimeType = fieldDefinition.outputType.namedType)
              ∨ ((TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool
                      schema
                    = true
                  ∧ objectTypeNameBool schema fieldDefinition.outputType.namedType = false
                  ∧ abstractRuntimeForFieldHeadDeep? schema parentType fieldName
                      arguments parentType rootSelectionSet
                    = some runtimeType))
            ∧ schema.typeIncludesObjectBool
                fieldDefinition.outputType.namedType runtimeType
              = true) := by
  intro hvalid hnormal hmem hlookup hcomposite hheadPromote
  by_cases hobject :
      objectTypeNameBool schema fieldDefinition.outputType.namedType = true
  · exact
      ⟨fieldDefinition.outputType.namedType,
        Or.inl ⟨hobject, rfl⟩,
        typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject⟩
  · have hnonObject :
        objectTypeNameBool schema fieldDefinition.outputType.namedType =
          false := by
      cases h : objectTypeNameBool schema fieldDefinition.outputType.namedType
      · rfl
      · contradiction
    rcases
        abstractRuntimeForFieldHeadDeep?_some_of_valid_normal_abstract_mem_lookup
          hvalid hnormal hmem hlookup hcomposite hnonObject with
      ⟨localRuntimeType, hlocalRuntime, _hlocalInclude⟩
    rcases
        hheadPromote parentType fieldName arguments localRuntimeType
          fieldDefinition hlookup hcomposite hnonObject hlocalRuntime with
      ⟨runtimeType, hrootRuntime, hinclude⟩
    exact
      ⟨runtimeType,
        Or.inr ⟨hcomposite, hnonObject, hrootRuntime⟩, hinclude⟩

theorem fieldCompositeSelectedChildRuntime_of_valid_normal_mem
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType responseName fieldName : Name}
    {arguments : List Argument} {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    : Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> ∃ runtimeType,
          (((objectTypeNameBool schema fieldDefinition.outputType.namedType = true
                ∧ runtimeType = fieldDefinition.outputType.namedType)
              ∨ ((TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool
                      schema
                    = true
                  ∧ objectTypeNameBool schema fieldDefinition.outputType.namedType = false
                  ∧ firstInlineFragmentTypeCondition? childSelectionSet
                    = some runtimeType))
            ∧ schema.typeIncludesObjectBool
                fieldDefinition.outputType.namedType runtimeType
              = true) := by
  intro hvalid hnormal hmem hlookup hcomposite
  by_cases hobject :
      objectTypeNameBool schema fieldDefinition.outputType.namedType = true
  · exact
      ⟨fieldDefinition.outputType.namedType,
        Or.inl ⟨hobject, rfl⟩,
        typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject⟩
  · have hnonObject :
        objectTypeNameBool schema fieldDefinition.outputType.namedType =
          false := by
      cases h : objectTypeNameBool schema fieldDefinition.outputType.namedType
      · rfl
      · contradiction
    rcases
        firstInlineFragmentTypeCondition?_some_of_valid_normal_abstract_field_mem_lookup
          hvalid hnormal hmem hlookup hcomposite hnonObject with
      ⟨runtimeType, hruntime, hinclude⟩
    exact
      ⟨runtimeType, Or.inr ⟨hcomposite, hnonObject, hruntime⟩,
        hinclude⟩

end GroundTypeNormalization

end NormalForm

end GraphQL
