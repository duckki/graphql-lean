import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.DiffObservable
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.ObservablePath
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.Readiness

/-!
Heterogeneous paired paths for focused normal-form uniqueness probes.

Unlike the matching-path relation, this relation permits the two sides to have
different normal parent types after a field-name mismatch.  It follows one
concrete executable branch on each side and records the first object layer at
which response keys or leaf/composite shapes already separate the executions.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

inductive NormalSelectionSetPairedPath (schema : Schema)
    : Name -> Name -> List Selection -> List Selection -> Prop where
  | objectLeftResponseName
    {leftParentType rightParentType responseName fieldName : Name}
    {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet left right : List Selection}
    : objectTypeNameBool schema leftParentType = true
      -> objectTypeNameBool schema rightParentType = true
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ left
      -> responseName ∉ right.filterMap Selection.responseName?
      -> NormalSelectionSetPairedPath schema leftParentType rightParentType left right

  | objectLeafPair
    {leftParentType rightParentType responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet left right : List Selection}
    {leftFieldDefinition rightFieldDefinition : FieldDefinition}
    : objectTypeNameBool schema leftParentType = true
      -> objectTypeNameBool schema rightParentType = true
      -> Selection.field responseName leftFieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName rightFieldName rightArguments
            rightDirectives rightChildSelectionSet
          ∈ right
      -> schema.lookupField leftParentType leftFieldName = some leftFieldDefinition
      -> schema.lookupField rightParentType rightFieldName = some rightFieldDefinition
      -> (TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> NormalSelectionSetPairedPath schema leftParentType rightParentType left right
  | objectCompositeLeftLeaf
    {leftParentType rightParentType responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet left right : List Selection}
    {leftFieldDefinition rightFieldDefinition : FieldDefinition}
    : objectTypeNameBool schema leftParentType = true
      -> objectTypeNameBool schema rightParentType = true
      -> Selection.field responseName leftFieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName rightFieldName rightArguments
            rightDirectives rightChildSelectionSet
          ∈ right
      -> schema.lookupField leftParentType leftFieldName = some leftFieldDefinition
      -> schema.lookupField rightParentType rightFieldName = some rightFieldDefinition
      -> (TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> NormalSelectionSetPairedPath schema leftParentType rightParentType left right
  | objectLeafCompositeRight
    {leftParentType rightParentType responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet left right : List Selection}
    {leftFieldDefinition rightFieldDefinition : FieldDefinition}
    : objectTypeNameBool schema leftParentType = true
      -> objectTypeNameBool schema rightParentType = true
      -> Selection.field responseName leftFieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName rightFieldName rightArguments
            rightDirectives rightChildSelectionSet
          ∈ right
      -> schema.lookupField leftParentType leftFieldName = some leftFieldDefinition
      -> schema.lookupField rightParentType rightFieldName = some rightFieldDefinition
      -> (TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> NormalSelectionSetPairedPath schema leftParentType rightParentType left right
  | objectCompositePair
    {leftParentType rightParentType responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet left right : List Selection}
    {leftFieldDefinition rightFieldDefinition : FieldDefinition}
    : objectTypeNameBool schema leftParentType = true
      -> objectTypeNameBool schema rightParentType = true
      -> Selection.field responseName leftFieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName rightFieldName rightArguments
            rightDirectives rightChildSelectionSet
          ∈ right
      -> schema.lookupField leftParentType leftFieldName = some leftFieldDefinition
      -> schema.lookupField rightParentType rightFieldName = some rightFieldDefinition
      -> (TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> NormalSelectionSetPairedPath schema
          leftFieldDefinition.outputType.namedType
          rightFieldDefinition.outputType.namedType leftChildSelectionSet
          rightChildSelectionSet
      -> NormalSelectionSetPairedPath schema leftParentType rightParentType left right
  | leftAbstract
    {leftParentType rightParentType typeCondition : Name}
    {directives : List DirectiveApplication}
    {leftChildSelectionSet left right : List Selection}
    : objectTypeNameBool schema leftParentType = false
      -> Selection.inlineFragment (some typeCondition) directives leftChildSelectionSet
          ∈ left
      -> NormalSelectionSetPairedPath schema typeCondition rightParentType
          leftChildSelectionSet right
      -> NormalSelectionSetPairedPath schema leftParentType rightParentType left right
  | rightAbstract
    {leftParentType rightParentType typeCondition : Name}
    {directives : List DirectiveApplication}
    {rightChildSelectionSet left right : List Selection}
    : objectTypeNameBool schema rightParentType = false
      -> Selection.inlineFragment (some typeCondition) directives rightChildSelectionSet
          ∈ right
      -> NormalSelectionSetPairedPath schema leftParentType typeCondition left
          rightChildSelectionSet
      -> NormalSelectionSetPairedPath schema leftParentType rightParentType left right

theorem normalSelectionSetPairedPath_of_valid_normal_nonempty_aux
    (n : Nat) {schema : Schema}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    {leftParentType rightParentType : Name}
    {left right : List Selection}
    : Validation.selectionSetValid schema leftVariableDefinitions leftParentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions
          rightParentType right
      -> selectionSetNormal schema leftParentType left
      -> selectionSetNormal schema rightParentType right
      -> left ≠ []
      -> right ≠ []
      -> SelectionSet.size left + SelectionSet.size right < n
      -> NormalSelectionSetPairedPath schema leftParentType rightParentType
          left right := by
  revert schema leftVariableDefinitions rightVariableDefinitions
    leftParentType rightParentType left right
  induction n using Nat.strongRecOn with
  | ind n ih =>
      intro schema leftVariableDefinitions rightVariableDefinitions
        leftParentType rightParentType left right hleftValid hrightValid
        hleftNormal hrightNormal hleftNonempty hrightNonempty hsize
      have hleftObservable :=
        normalSelectionSetObservableLeaf_of_valid_normal_nonempty schema
          leftParentType leftVariableDefinitions left hleftValid hleftNormal
          hleftNonempty
      by_cases hleftObject :
          objectTypeNameBool schema leftParentType = true
      · by_cases hrightObject :
            objectTypeNameBool schema rightParentType = true
        · cases hleftObservable with
          | objectLeaf hleftObjectPath hleftMem hleftLookup hleftLeaf =>
              rename_i responseName leftFieldName leftArguments
                leftDirectives leftChildSelectionSet
                leftFieldDefinition
              by_cases hrightHasResponseName :
                  responseName ∈
                    right.filterMap Selection.responseName?
              · rcases
                    selectionSetNormal_field_mem_of_object_responseName_mem
                      hrightNormal hrightObject hrightHasResponseName with
                  ⟨rightFieldName, rightArguments, rightDirectives,
                    rightChildSelectionSet, hrightMem⟩
                rcases
                    selectionSetValid_field_lookup_leaf_or_composite_child
                      hrightValid hrightMem with
                  ⟨rightFieldDefinition, hrightLookup, hrightKind⟩
                rcases hrightKind with hrightLeaf | hrightComposite
                · exact
                    NormalSelectionSetPairedPath.objectLeafPair
                      hleftObject hrightObject hleftMem hrightMem
                      hleftLookup hrightLookup hleftLeaf hrightLeaf.1
                · exact
                    NormalSelectionSetPairedPath.objectLeafCompositeRight
                      hleftObject hrightObject hleftMem hrightMem
                      hleftLookup hrightLookup hleftLeaf
                      (typeRef_named_isCompositeBool_of_isCompositeType
                        hrightComposite.1)
              · exact
                  NormalSelectionSetPairedPath.objectLeftResponseName
                    hleftObject hrightObject hleftMem
                    hrightHasResponseName
          | objectChild hleftObjectPath hleftMem hleftLookup
              hleftComposite hleftChildObservable =>
              rename_i responseName leftFieldName leftArguments
                leftDirectives leftChildSelectionSet
                leftFieldDefinition
              by_cases hrightHasResponseName :
                  responseName ∈
                    right.filterMap Selection.responseName?
              · rcases
                    selectionSetNormal_field_mem_of_object_responseName_mem
                      hrightNormal hrightObject hrightHasResponseName with
                  ⟨rightFieldName, rightArguments, rightDirectives,
                    rightChildSelectionSet, hrightMem⟩
                rcases
                    selectionSetValid_field_lookup_leaf_or_composite_child
                      hrightValid hrightMem with
                  ⟨rightFieldDefinition, hrightLookup, hrightKind⟩
                rcases hrightKind with hrightLeaf | hrightComposite
                · exact
                    NormalSelectionSetPairedPath.objectCompositeLeftLeaf
                      hleftObject hrightObject hleftMem hrightMem
                      hleftLookup hrightLookup
                      (typeRef_named_isCompositeBool_of_isCompositeType
                        hleftComposite)
                      hrightLeaf.1
                · have hleftChildValid :
                      Validation.selectionSetValid schema
                        leftVariableDefinitions
                        leftFieldDefinition.outputType.namedType
                        leftChildSelectionSet := by
                    rcases
                        selectionSetValid_field_lookup_leaf_or_composite_child
                          hleftValid hleftMem with
                      ⟨candidateDefinition, hcandidateLookup, hkind⟩
                    have hcandidateEq :
                        candidateDefinition = leftFieldDefinition := by
                      rw [hleftLookup] at hcandidateLookup
                      exact Option.some.inj hcandidateLookup.symm
                    subst candidateDefinition
                    rcases hkind with hleaf | hcompositeKind
                    · rw [typeRef_named_isCompositeBool_of_isCompositeType
                        hleftComposite] at hleaf
                      simp at hleaf
                    · exact hcompositeKind.2.2
                  have hleftChildNonempty :
                      leftChildSelectionSet ≠ [] :=
                    selectionSet_nonempty_of_normalSelectionSetObservableLeaf
                      hleftChildObservable
                  have hleftChildNormal :
                      selectionSetNormal schema
                        leftFieldDefinition.outputType.namedType
                        leftChildSelectionSet :=
                    selectionSetNormal_field_child_of_mem_lookup hleftNormal
                      hleftMem hleftLookup
                  have hrightChildNormal :
                      selectionSetNormal schema
                        rightFieldDefinition.outputType.namedType
                        rightChildSelectionSet :=
                    selectionSetNormal_field_child_of_mem_lookup hrightNormal
                      hrightMem hrightLookup
                  have hleftChildSize :=
                    selectionSet_size_field_child_lt_of_mem
                      (selectionSet := left) hleftMem
                  have hrightChildSize :=
                    selectionSet_size_field_child_lt_of_mem
                      (selectionSet := right) hrightMem
                  have hchildPath :=
                    ih
                      (SelectionSet.size leftChildSelectionSet +
                        SelectionSet.size rightChildSelectionSet + 1)
                      (by omega) hleftChildValid hrightComposite.2.2
                      hleftChildNormal hrightChildNormal
                      hleftChildNonempty hrightComposite.2.1 (by omega)
                  exact
                    NormalSelectionSetPairedPath.objectCompositePair
                      hleftObject hrightObject hleftMem hrightMem
                      hleftLookup hrightLookup
                      (typeRef_named_isCompositeBool_of_isCompositeType
                        hleftComposite)
                      (typeRef_named_isCompositeBool_of_isCompositeType
                        hrightComposite.1)
                      hchildPath
              · exact
                  NormalSelectionSetPairedPath.objectLeftResponseName
                    hleftObject hrightObject hleftMem
                    hrightHasResponseName
          | abstractInlineFragment hleftNonObject =>
              rw [hleftObject] at hleftNonObject
              simp at hleftNonObject
        · have hrightNonObject :
              objectTypeNameBool schema rightParentType = false := by
            cases h : objectTypeNameBool schema rightParentType <;>
              simp [h] at hrightObject ⊢
          have hrightObservable :=
            normalSelectionSetObservableLeaf_of_valid_normal_nonempty schema
              rightParentType rightVariableDefinitions right hrightValid
              hrightNormal hrightNonempty
          cases hrightObservable with
          | objectLeaf hrightObjectPath =>
              rw [hrightNonObject] at hrightObjectPath
              simp at hrightObjectPath
          | objectChild hrightObjectPath =>
              rw [hrightNonObject] at hrightObjectPath
              simp at hrightObjectPath
          | abstractInlineFragment _hrightNonObject hrightMem
              hrightChildObservable =>
              rename_i typeCondition directives rightChildSelectionSet
              have hrightChildValid :=
                selectionSetValid_inlineFragment_some_child_of_mem
                  hrightValid hrightMem
              rcases
                  selectionSetNormal_inlineFragment_child_of_mem hrightNormal
                    hrightMem with
                ⟨_htypeObject, hrightChildNormal⟩
              have hrightChildSize :=
                selectionSet_size_inlineFragment_child_lt_of_mem
                  (selectionSet := right) hrightMem
              have hchildPath :=
                ih
                  (SelectionSet.size left +
                    SelectionSet.size rightChildSelectionSet + 1)
                  (by omega) hleftValid hrightChildValid hleftNormal
                  hrightChildNormal hleftNonempty
                  (selectionSetValid_inlineFragment_some_child_nonempty_of_mem
                    hrightValid hrightMem)
                  (by omega)
              exact
                NormalSelectionSetPairedPath.rightAbstract
                  hrightNonObject hrightMem hchildPath
      · have hleftNonObject :
            objectTypeNameBool schema leftParentType = false := by
          cases h : objectTypeNameBool schema leftParentType <;>
            simp [h] at hleftObject ⊢
        cases hleftObservable with
        | objectLeaf hleftObjectPath =>
            rw [hleftNonObject] at hleftObjectPath
            simp at hleftObjectPath
        | objectChild hleftObjectPath =>
            rw [hleftNonObject] at hleftObjectPath
            simp at hleftObjectPath
        | abstractInlineFragment _hleftNonObject hleftMem
            hleftChildObservable =>
            rename_i typeCondition directives leftChildSelectionSet
            have hleftChildValid :=
              selectionSetValid_inlineFragment_some_child_of_mem hleftValid
                hleftMem
            rcases
                selectionSetNormal_inlineFragment_child_of_mem hleftNormal
                  hleftMem with
              ⟨_htypeObject, hleftChildNormal⟩
            have hleftChildSize :=
              selectionSet_size_inlineFragment_child_lt_of_mem
                (selectionSet := left) hleftMem
            have hchildPath :=
              ih
                (SelectionSet.size leftChildSelectionSet +
                  SelectionSet.size right + 1)
                (by omega) hleftChildValid hrightValid hleftChildNormal
                hrightNormal
                (selectionSetValid_inlineFragment_some_child_nonempty_of_mem
                  hleftValid hleftMem)
                hrightNonempty (by omega)
            exact
              NormalSelectionSetPairedPath.leftAbstract hleftNonObject
                hleftMem hchildPath

theorem normalSelectionSetPairedPath_of_valid_normal_nonempty
    {schema : Schema}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    {leftParentType rightParentType : Name}
    {left right : List Selection}
    : Validation.selectionSetValid schema leftVariableDefinitions leftParentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions
          rightParentType right
      -> selectionSetNormal schema leftParentType left
      -> selectionSetNormal schema rightParentType right
      -> left ≠ []
      -> right ≠ []
      -> NormalSelectionSetPairedPath schema leftParentType rightParentType
          left right := by
  intro hleftValid hrightValid hleftNormal hrightNormal hleftNonempty
    hrightNonempty
  exact
    normalSelectionSetPairedPath_of_valid_normal_nonempty_aux
      (SelectionSet.size left + SelectionSet.size right + 1)
      hleftValid hrightValid hleftNormal hrightNormal hleftNonempty
      hrightNonempty (by omega)

end GroundTypeNormalization

end NormalForm

end GraphQL
