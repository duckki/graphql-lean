import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.Readiness

/-!
Observable leaf paths for normal selection sets.

The tagged semantic separator ultimately needs a concrete field below a
possibly-composite selection.  This module proves the proof-only syntactic fact
that a valid, normal, nonempty selection set always contains such a finite path.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

inductive NormalSelectionSetObservableLeaf (schema : Schema)
    : Name -> List Selection -> Prop where
  | objectLeaf
    {parentType responseName fieldName : Name}
    {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    : objectTypeNameBool schema parentType = true
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> NormalSelectionSetObservableLeaf schema parentType selectionSet
  | objectChild
    {parentType responseName fieldName : Name}
    {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    : objectTypeNameBool schema parentType = true
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> schema.isCompositeType fieldDefinition.outputType.namedType
      -> NormalSelectionSetObservableLeaf schema
          fieldDefinition.outputType.namedType childSelectionSet
      -> NormalSelectionSetObservableLeaf schema parentType selectionSet
  | abstractInlineFragment
    {parentType typeCondition : Name}
    {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    : objectTypeNameBool schema parentType = false
      -> Selection.inlineFragment (some typeCondition) directives childSelectionSet
          ∈ selectionSet
      -> NormalSelectionSetObservableLeaf schema typeCondition childSelectionSet
      -> NormalSelectionSetObservableLeaf schema parentType selectionSet

theorem normalSelectionSetObservableLeaf_of_valid_normal_nonempty (schema : Schema)
    : ∀ parentType variableDefinitions (selectionSet : List Selection),
        Validation.selectionSetValid schema variableDefinitions parentType selectionSet
        -> selectionSetNormal schema parentType selectionSet
        -> selectionSet ≠ []
        -> NormalSelectionSetObservableLeaf schema parentType selectionSet
  | parentType, variableDefinitions, selectionSet, hvalid, hnormal,
      hnonempty => by
      by_cases hparentObject : objectTypeNameBool schema parentType = true
      · rcases
          selectionSetNormal_field_mem_of_object_nonempty hnormal
            hparentObject hnonempty with
          ⟨responseName, fieldName, arguments, directives,
            childSelectionSet, hmem⟩
        rcases
          selectionSetValid_field_lookup_leaf_or_composite_child hvalid
            hmem with
          ⟨fieldDefinition, hlookup, hkind⟩
        rcases hkind with hleaf | hcomposite
        · exact
            NormalSelectionSetObservableLeaf.objectLeaf hparentObject hmem
              hlookup hleaf.1
        · have hchildNormal :
              selectionSetNormal schema fieldDefinition.outputType.namedType
                childSelectionSet :=
            selectionSetNormal_field_child_of_mem_lookup hnormal hmem
              hlookup
          have hchildSize :
              SelectionSet.size childSelectionSet <
                SelectionSet.size selectionSet :=
            selectionSet_size_field_child_lt_of_mem hmem
          have hchildPath :
              NormalSelectionSetObservableLeaf schema
                fieldDefinition.outputType.namedType childSelectionSet :=
            normalSelectionSetObservableLeaf_of_valid_normal_nonempty schema
              fieldDefinition.outputType.namedType variableDefinitions
              childSelectionSet hcomposite.2.2 hchildNormal
              hcomposite.2.1
          exact
            NormalSelectionSetObservableLeaf.objectChild hparentObject hmem
              hlookup hcomposite.1 hchildPath
      · have hparentAbstract :
            objectTypeNameBool schema parentType = false := by
          cases h : objectTypeNameBool schema parentType
          · rfl
          · exact False.elim (hparentObject h)
        cases selectionSet with
        | nil =>
            exact False.elim (hnonempty rfl)
        | cons selection rest =>
            rcases
              selectionSetNormal_inlineFragment_some_of_nonObject_mem
                hnormal hparentAbstract
                (by simp : selection ∈ selection :: rest) with
              ⟨typeCondition, directives, childSelectionSet,
                hselection⟩
            subst selection
            have hmem :
                Selection.inlineFragment (some typeCondition) directives
                    childSelectionSet ∈
                  Selection.inlineFragment (some typeCondition) directives
                    childSelectionSet :: rest := by
              simp
            rcases selectionSetNormal_inlineFragment_child_of_mem hnormal
                hmem with
              ⟨_htypeObject, hchildNormal⟩
            have hchildValid :
                Validation.selectionSetValid schema variableDefinitions
                  typeCondition childSelectionSet :=
              selectionSetValid_inlineFragment_some_child_of_mem hvalid
                hmem
            have hchildSize :
                SelectionSet.size childSelectionSet <
                  SelectionSet.size
                    (Selection.inlineFragment (some typeCondition) directives
                      childSelectionSet :: rest) :=
              selectionSet_size_inlineFragment_child_lt_of_mem hmem
            have hchildPath :
                NormalSelectionSetObservableLeaf schema typeCondition
                  childSelectionSet :=
              normalSelectionSetObservableLeaf_of_valid_normal_nonempty schema
                typeCondition variableDefinitions childSelectionSet
                hchildValid hchildNormal
                (selectionSetValid_inlineFragment_some_child_nonempty_of_mem
                  hvalid hmem)
            exact
              NormalSelectionSetObservableLeaf.abstractInlineFragment
                hparentAbstract hmem hchildPath
termination_by _parentType _variableDefinitions selectionSet =>
  SelectionSet.size selectionSet
decreasing_by
  all_goals
    simp_wf
    simp_all

end GroundTypeNormalization

end NormalForm

end GraphQL
