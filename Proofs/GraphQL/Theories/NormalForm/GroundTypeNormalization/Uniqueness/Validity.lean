import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.SyntaxDiff
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Validity.Support.Basics
import Proofs.GraphQL.Validation.SelectionValidity

/-!
Validity projections used by the ground-type normal-form uniqueness proof.

These lemmas keep the semantic separation proof from repeatedly unfolding
`selectionSetValid` and `fieldSelectionSetValid` at arbitrary list members.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

theorem fieldSelectionSetValid_child_of_nonempty
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {fieldDefinition : FieldDefinition} {selectionSet : List Selection}
    : Validation.fieldSelectionSetValid schema variableDefinitions
        fieldDefinition selectionSet
      -> selectionSet ≠ []
      -> schema.isCompositeType fieldDefinition.outputType.namedType
          ∧ Validation.selectionSetValid schema variableDefinitions
              fieldDefinition.outputType.namedType selectionSet := by
  intro hvalid hnonempty
  simp [Validation.fieldSelectionSetValid] at hvalid
  rcases hvalid with ⟨_houtput, hleaf | hcomposite⟩
  · exact False.elim (hnonempty hleaf.2)
  · exact ⟨hcomposite.1, hcomposite.2.2⟩

theorem fieldSelectionSetValid_child_of_composite
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {fieldDefinition : FieldDefinition} {selectionSet : List Selection}
    : Validation.fieldSelectionSetValid schema variableDefinitions
        fieldDefinition selectionSet
      -> schema.isCompositeType fieldDefinition.outputType.namedType
      -> selectionSet ≠ []
          ∧ Validation.selectionSetValid schema variableDefinitions
              fieldDefinition.outputType.namedType selectionSet := by
  intro hvalid hcomposite
  simp [Validation.fieldSelectionSetValid] at hvalid
  rcases hvalid with ⟨_houtput, hleaf | hchild⟩
  · exact False.elim (isLeafType_not_isCompositeType hleaf.1 hcomposite)
  · exact ⟨hchild.2.1, hchild.2.2⟩

theorem fieldDefinition_namedType_eq_of_fieldReturnType?
    {schema : Schema} {parentType fieldName returnType : Name}
    {fieldDefinition : FieldDefinition}
    : schema.lookupField parentType fieldName = some fieldDefinition
      -> schema.fieldReturnType? parentType fieldName = some returnType
      -> fieldDefinition.outputType.namedType = returnType := by
  intro hlookup hreturnType
  simp [Schema.fieldReturnType?, hlookup] at hreturnType
  exact hreturnType

theorem normalSelectionSetDiff_left_or_right_nonempty
    {schema : Schema} {parentType : Name} {left right : List Selection}
    : NormalSelectionSetDiff schema parentType left right -> left ≠ [] ∨ right ≠ [] := by
  intro hdiff
  cases hdiff with
  | objectLeftResponseName hobject hmem hrightNo =>
      exact Or.inl (List.ne_nil_of_mem hmem)
  | objectRightResponseName hobject hmem hleftNo =>
      exact Or.inr (List.ne_nil_of_mem hmem)
  | objectFieldName hobject hleftMem hrightMem hfield =>
      exact Or.inl (List.ne_nil_of_mem hleftMem)
  | objectArguments hobject hleftMem hrightMem harguments =>
      exact Or.inl (List.ne_nil_of_mem hleftMem)
  | objectChild hobject hreturn hleftMem hrightMem harguments hchild =>
      exact Or.inl (List.ne_nil_of_mem hleftMem)
  | abstractLeftTypeCondition hobject hmem hrightNo =>
      exact Or.inl (List.ne_nil_of_mem hmem)
  | abstractRightTypeCondition hobject hmem hleftNo =>
      exact Or.inr (List.ne_nil_of_mem hmem)
  | abstractChild hobject hleftMem hrightMem hchild =>
      exact Or.inl (List.ne_nil_of_mem hleftMem)

theorem selectionSetValid_selectionValid_of_mem
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType : Name} {selectionSet : List Selection}
    {selection : Selection}
    : Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> selection ∈ selectionSet
      -> Validation.selectionValid schema variableDefinitions parentType selection := by
  intro hvalid hmem
  simp [Validation.selectionSetValid] at hvalid
  exact hvalid selection hmem

theorem selectionSetValid_field_lookup_of_mem
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    : Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> ∃ fieldDefinition,
          schema.lookupField parentType fieldName = some fieldDefinition
          ∧ Validation.argumentsValid schema fieldDefinition.arguments
              variableDefinitions arguments
          ∧ Validation.fieldSelectionSetValid schema variableDefinitions
              fieldDefinition childSelectionSet := by
  intro hvalid hmem
  exact Validation.selectionValid_field_lookup
    (selectionSetValid_selectionValid_of_mem hvalid hmem)

theorem selectionSetValid_field_child_of_mem
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    : Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> childSelectionSet ≠ []
      -> ∃ fieldDefinition,
          schema.lookupField parentType fieldName = some fieldDefinition
          ∧ schema.isCompositeType fieldDefinition.outputType.namedType
          ∧ Validation.selectionSetValid schema variableDefinitions
              fieldDefinition.outputType.namedType childSelectionSet := by
  intro hvalid hmem hnonempty
  rcases selectionSetValid_field_lookup_of_mem hvalid hmem with
    ⟨fieldDefinition, hlookup, _harguments, hfieldSelectionSet⟩
  rcases fieldSelectionSetValid_child_of_nonempty hfieldSelectionSet
      hnonempty with
    ⟨hcomposite, hchildValid⟩
  exact ⟨fieldDefinition, hlookup, hcomposite, hchildValid⟩

theorem selectionSetValid_field_children_of_diff {schema : Schema}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    {parentType returnType responseName fieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet left right : List Selection}
    : Validation.selectionSetValid schema leftVariableDefinitions parentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
      -> Selection.field responseName fieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName fieldName rightArguments rightDirectives
            rightChildSelectionSet
          ∈ right
      -> schema.fieldReturnType? parentType fieldName = some returnType
      -> NormalSelectionSetDiff schema returnType leftChildSelectionSet
          rightChildSelectionSet
      -> ∃ fieldDefinition,
          schema.lookupField parentType fieldName = some fieldDefinition
          ∧ fieldDefinition.outputType.namedType = returnType
          ∧ Validation.selectionSetValid schema leftVariableDefinitions
              returnType leftChildSelectionSet
          ∧ Validation.selectionSetValid schema rightVariableDefinitions
              returnType rightChildSelectionSet := by
  intro hleftValid hrightValid hleftMem hrightMem hreturnType hdiff
  rcases selectionSetValid_field_lookup_of_mem hleftValid hleftMem with
    ⟨fieldDefinition, hlookup, _hleftArguments, hleftFieldValid⟩
  rcases selectionSetValid_field_lookup_of_mem hrightValid hrightMem with
    ⟨rightFieldDefinition, hrightLookup, _hrightArguments,
      hrightFieldValid⟩
  have hrightFieldDefinition : rightFieldDefinition = fieldDefinition := by
    rw [hlookup] at hrightLookup
    exact Option.some.inj hrightLookup.symm
  subst rightFieldDefinition
  have hnamedType :
      fieldDefinition.outputType.namedType = returnType :=
    fieldDefinition_namedType_eq_of_fieldReturnType? hlookup hreturnType
  have hnonempty :=
    normalSelectionSetDiff_left_or_right_nonempty hdiff
  have hcomposite :
      schema.isCompositeType fieldDefinition.outputType.namedType := by
    rcases hnonempty with hleftNonempty | hrightNonempty
    · exact (fieldSelectionSetValid_child_of_nonempty hleftFieldValid hleftNonempty).1
    · exact (fieldSelectionSetValid_child_of_nonempty hrightFieldValid hrightNonempty).1
  rcases fieldSelectionSetValid_child_of_composite hleftFieldValid
      hcomposite with
    ⟨_hleftNonempty, hleftChildValid⟩
  rcases fieldSelectionSetValid_child_of_composite hrightFieldValid
      hcomposite with
    ⟨_hrightNonempty, hrightChildValid⟩
  refine ⟨fieldDefinition, hlookup, hnamedType, ?_, ?_⟩
  · simpa [hnamedType] using hleftChildValid
  · simpa [hnamedType] using hrightChildValid

theorem selectionSetValid_inlineFragment_none_child_of_mem
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType : Name} {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    : Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> Selection.inlineFragment none directives childSelectionSet ∈ selectionSet
      -> Validation.selectionSetValid schema variableDefinitions parentType
          childSelectionSet := by
  intro hvalid hmem
  exact Validation.selectionValid_inlineFragment_none_selectionSetValid
    (selectionSetValid_selectionValid_of_mem hvalid hmem)

theorem selectionSetValid_inlineFragment_some_child_of_mem
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType typeCondition : Name}
    {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    : Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> Selection.inlineFragment (some typeCondition) directives childSelectionSet
          ∈ selectionSet
      -> Validation.selectionSetValid schema variableDefinitions typeCondition
          childSelectionSet := by
  intro hvalid hmem
  exact Validation.selectionValid_inlineFragment_some_selectionSetValid
    (selectionSetValid_selectionValid_of_mem hvalid hmem)

theorem selectionSetValid_inlineFragment_some_child_nonempty_of_mem
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType typeCondition : Name}
    {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    : Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> Selection.inlineFragment (some typeCondition) directives childSelectionSet
          ∈ selectionSet
      -> childSelectionSet ≠ [] := by
  intro hvalid hmem
  have hselectionValid :=
    selectionSetValid_selectionValid_of_mem hvalid hmem
  simp [Validation.selectionValid] at hselectionValid
  exact hselectionValid.2.2.2.1

theorem selectionSetValid_inlineFragment_some_typesOverlap_of_mem
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType typeCondition : Name}
    {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    : Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> Selection.inlineFragment (some typeCondition) directives childSelectionSet
          ∈ selectionSet
      -> schema.typesOverlap parentType typeCondition := by
  intro hvalid hmem
  have hselectionValid :=
    selectionSetValid_selectionValid_of_mem hvalid hmem
  simp [Validation.selectionValid] at hselectionValid
  exact hselectionValid.2.2.1

theorem typeIncludesObjectBool_of_typesOverlap_object
    (schema : Schema) {parentType objectType : Name}
    : schema.typesOverlap parentType objectType
      -> schema.objectType objectType
      -> schema.typeIncludesObjectBool parentType objectType = true := by
  intro hoverlap hobject
  rcases hoverlap with ⟨overlapObject, hparentIncludes, hobjectIncludes⟩
  have hoverlapEq : overlapObject = objectType :=
    object_typeIncludesObjectBool_eq_self schema hobject
      (List.contains_iff_mem.mpr hobjectIncludes)
  subst overlapObject
  exact List.contains_iff_mem.mpr hparentIncludes

theorem field_child_inlineFragment_child_valid_free_normal
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType returnType responseName fieldName typeCondition : Name}
    {arguments : List Argument}
    {directives inlineDirectives : List DirectiveApplication}
    {childSelectionSet inlineChildSelectionSet selectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    : Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> selectionSetDirectiveFree selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> fieldDefinition.outputType.namedType = returnType
      -> Selection.inlineFragment (some typeCondition) inlineDirectives
            inlineChildSelectionSet
          ∈ childSelectionSet
      -> inlineDirectives = []
          ∧ Validation.selectionSetValid schema variableDefinitions
              typeCondition inlineChildSelectionSet
          ∧ selectionSetDirectiveFree inlineChildSelectionSet
          ∧ objectTypeNameBool schema typeCondition = true
          ∧ schema.typeIncludesObjectBool returnType typeCondition = true
          ∧ selectionSetNormal schema typeCondition inlineChildSelectionSet := by
  intro hvalid hfree hnormal hfieldMem hlookup hreturnType hinlineMem
  rcases selectionSetValid_field_lookup_of_mem hvalid hfieldMem with
    ⟨candidateFieldDefinition, hcandidateLookup, _hargumentsValid,
      hfieldValid⟩
  have hcandidateEq : candidateFieldDefinition = fieldDefinition := by
    rw [hlookup] at hcandidateLookup
    exact Option.some.inj hcandidateLookup.symm
  subst candidateFieldDefinition
  have hchildNonempty : childSelectionSet ≠ [] :=
    List.ne_nil_of_mem hinlineMem
  rcases fieldSelectionSetValid_child_of_nonempty hfieldValid
      hchildNonempty with
    ⟨_hcomposite, hchildValidRaw⟩
  have hchildValid :
      Validation.selectionSetValid schema variableDefinitions returnType
        childSelectionSet := by
    simpa [hreturnType] using hchildValidRaw
  have hchildFree : selectionSetDirectiveFree childSelectionSet :=
    selectionSetDirectiveFree_field_child_of_mem hfree hfieldMem
  have hchildNormal :
      selectionSetNormal schema returnType childSelectionSet := by
    rcases selectionSetNormal_field_child_of_mem_with_returnType hnormal
        hfieldMem with
      ⟨candidateReturnType, hcandidateReturnType, hcandidateNormal⟩
    have hcandidateReturnEq : candidateReturnType = returnType := by
      simp [Schema.fieldReturnType?, hlookup, hreturnType] at hcandidateReturnType
      exact hcandidateReturnType.symm
    subst candidateReturnType
    exact hcandidateNormal
  have hinlineDirectives : inlineDirectives = [] :=
    selectionSetDirectiveFree_inlineFragment_directives_nil_of_mem
      hchildFree hinlineMem
  have hinlineValid :
      Validation.selectionSetValid schema variableDefinitions typeCondition
        inlineChildSelectionSet :=
    selectionSetValid_inlineFragment_some_child_of_mem hchildValid
      hinlineMem
  have hinlineFree :
      selectionSetDirectiveFree inlineChildSelectionSet :=
    selectionSetDirectiveFree_inlineFragment_child_of_mem hchildFree
      hinlineMem
  rcases selectionSetNormal_inlineFragment_child_of_mem hchildNormal
      hinlineMem with
    ⟨htypeObject, hinlineNormal⟩
  have hchildOverlap : schema.typesOverlap returnType typeCondition :=
    selectionSetValid_inlineFragment_some_typesOverlap_of_mem hchildValid
      hinlineMem
  have hinclude :
      schema.typeIncludesObjectBool returnType typeCondition = true :=
    typeIncludesObjectBool_of_typesOverlap_object schema hchildOverlap
      htypeObject
  have htypeObjectBool : objectTypeNameBool schema typeCondition = true :=
    objectTypeNameBool_eq_true_of_objectType_forNormality schema
      htypeObject
  exact ⟨
    hinlineDirectives,
    hinlineValid,
    hinlineFree,
    htypeObjectBool,
    hinclude,
    hinlineNormal
  ⟩

end GroundTypeNormalization

end NormalForm

end GraphQL
