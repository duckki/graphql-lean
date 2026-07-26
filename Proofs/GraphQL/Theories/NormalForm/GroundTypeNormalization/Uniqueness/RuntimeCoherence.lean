import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.BoundaryProbe

/-!
Runtime-coherence support for focused normal-form uniqueness proofs.

This module contains the reusable runtime-active and root-coherence invariants
used by focused path and contextual witness constructions.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

theorem firstInlineFragmentTypeCondition?_some_mem_filterMap
    {selectionSet : List Selection} {typeCondition : Name}
    : firstInlineFragmentTypeCondition? selectionSet = some typeCondition
      -> typeCondition ∈ selectionSet.filterMap inlineFragmentTypeCondition? := by
  intro hfirst
  induction selectionSet with
  | nil =>
      simp [firstInlineFragmentTypeCondition?] at hfirst
  | cons selection rest ih =>
      cases selection with
      | field responseName fieldName arguments directives childSelectionSet =>
          have htail :
              typeCondition ∈ rest.filterMap inlineFragmentTypeCondition? :=
            ih (by
              simpa [firstInlineFragmentTypeCondition?] using hfirst)
          simpa [inlineFragmentTypeCondition?] using htail
      | inlineFragment maybeTypeCondition directives childSelectionSet =>
          cases maybeTypeCondition with
          | none =>
              have htail :
                  typeCondition ∈ rest.filterMap inlineFragmentTypeCondition? :=
                ih (by
                  simpa [firstInlineFragmentTypeCondition?] using hfirst)
              simpa [inlineFragmentTypeCondition?] using htail
          | some headTypeCondition =>
              have hsame : headTypeCondition = typeCondition := by
                simpa [firstInlineFragmentTypeCondition?] using hfirst
              subst headTypeCondition
              simp [inlineFragmentTypeCondition?]

def selectionSetRuntimeAligned
    (schema : Schema) (parentType runtimeType : Name)
    (selectionSet : List Selection)
    : Prop :=
  (objectTypeNameBool schema parentType = true ∧ runtimeType = parentType)
  ∨ (objectTypeNameBool schema parentType = false
      ∧ firstInlineFragmentTypeCondition? selectionSet = some runtimeType)

theorem selectionSetRuntimeAligned_object
    {schema : Schema} {parentType : Name} {selectionSet : List Selection}
    : objectTypeNameBool schema parentType = true
      -> selectionSetRuntimeAligned schema parentType parentType selectionSet := by
  intro hobject
  exact Or.inl ⟨hobject, rfl⟩

theorem selectionSetRuntimeAligned_runtime_eq_of_object
    {schema : Schema} {parentType runtimeType : Name}
    {selectionSet : List Selection}
    : objectTypeNameBool schema parentType = true
      -> selectionSetRuntimeAligned schema parentType runtimeType selectionSet
      -> runtimeType = parentType := by
  intro hobject haligned
  rcases haligned with hobjectAligned | habstractAligned
  · exact hobjectAligned.2
  · rw [hobject] at habstractAligned
    simp at habstractAligned

theorem selectionSetRuntimeAligned_firstInline_of_abstract
    {schema : Schema} {parentType runtimeType : Name}
    {selectionSet : List Selection}
    : objectTypeNameBool schema parentType = false
      -> selectionSetRuntimeAligned schema parentType runtimeType selectionSet
      -> firstInlineFragmentTypeCondition? selectionSet = some runtimeType := by
  intro hnonObject haligned
  rcases haligned with hobjectAligned | habstractAligned
  · rw [hnonObject] at hobjectAligned
    simp at hobjectAligned
  · exact habstractAligned.2

theorem selectionSetRuntimeAligned_typeIncludes_of_normal
    {schema : Schema} {parentType runtimeType : Name}
    {variableDefinitions : List VariableDefinition}
    {selectionSet : List Selection}
    : Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> selectionSetRuntimeAligned schema parentType runtimeType selectionSet
      -> schema.typeIncludesObjectBool parentType runtimeType = true := by
  intro hvalid hnormal haligned
  rcases haligned with hobjectAligned | habstractAligned
  · rcases hobjectAligned with ⟨hobject, hruntime⟩
    subst runtimeType
    exact typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject
  · rcases habstractAligned with ⟨_hnonObject, hfirst⟩
    have hmemFilter :
        runtimeType ∈ selectionSet.filterMap inlineFragmentTypeCondition? :=
      firstInlineFragmentTypeCondition?_some_mem_filterMap hfirst
    rcases List.mem_filterMap.mp hmemFilter with
      ⟨selection, hmem, hcondition⟩
    cases selection with
    | field responseName fieldName arguments directives childSelectionSet =>
        simp [inlineFragmentTypeCondition?] at hcondition
    | inlineFragment maybeTypeCondition directives childSelectionSet =>
        cases maybeTypeCondition with
        | none =>
            simp [inlineFragmentTypeCondition?] at hcondition
        | some typeCondition =>
            have htypeEq : typeCondition = runtimeType := by
              simpa [inlineFragmentTypeCondition?] using hcondition
            subst typeCondition
            rcases selectionSetNormal_inlineFragment_child_of_mem hnormal hmem
              with ⟨htypeObject, _hchildNormal⟩
            have hoverlap : schema.typesOverlap parentType runtimeType :=
              selectionSetValid_inlineFragment_some_typesOverlap_of_mem
                hvalid hmem
            exact typeIncludesObjectBool_of_typesOverlap_object schema
              hoverlap htypeObject

theorem selectionSetRuntimeAligned_runtime_object_of_normal
    {schema : Schema} {parentType runtimeType : Name}
    {variableDefinitions : List VariableDefinition}
    {selectionSet : List Selection}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> selectionSetRuntimeAligned schema parentType runtimeType selectionSet
      -> objectTypeNameBool schema runtimeType = true := by
  intro hschema hvalid hnormal haligned
  exact
    objectTypeNameBool_of_typeIncludesObjectBool hschema
      (selectionSetRuntimeAligned_typeIncludes_of_normal hvalid hnormal
        haligned)

def selectionSetRuntimeActive
    (schema : Schema) (parentType runtimeType : Name)
    (selectionSet : List Selection)
    : Prop :=
  (objectTypeNameBool schema parentType = true ∧ runtimeType = parentType)
  ∨ (objectTypeNameBool schema parentType = false
      ∧ ∃ directives bodySelectionSet,
          Selection.inlineFragment (some runtimeType) directives bodySelectionSet
            ∈ selectionSet
          ∧ bodySelectionSet ≠ []
          ∧ selectionSetNormal schema runtimeType bodySelectionSet)

theorem selectionSetRuntimeActive_object
    {schema : Schema} {parentType : Name} {selectionSet : List Selection}
    : objectTypeNameBool schema parentType = true
      -> selectionSetRuntimeActive schema parentType parentType selectionSet := by
  intro hobject
  exact Or.inl ⟨hobject, rfl⟩

theorem selectionSetRuntimeActive_runtime_eq_of_object
    {schema : Schema} {parentType runtimeType : Name}
    {selectionSet : List Selection}
    : objectTypeNameBool schema parentType = true
      -> selectionSetRuntimeActive schema parentType runtimeType selectionSet
      -> runtimeType = parentType := by
  intro hobject hactive
  rcases hactive with hobjectActive | habstractActive
  · exact hobjectActive.2
  · rw [hobject] at habstractActive
    simp at habstractActive

theorem selectionSetRuntimeActive_typeIncludes_of_normal
    {schema : Schema} {parentType runtimeType : Name}
    {variableDefinitions : List VariableDefinition}
    {selectionSet : List Selection}
    : Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> selectionSetRuntimeActive schema parentType runtimeType selectionSet
      -> schema.typeIncludesObjectBool parentType runtimeType = true := by
  intro hvalid hnormal hactive
  rcases hactive with hobjectActive | habstractActive
  · rcases hobjectActive with ⟨hobject, hruntime⟩
    subst runtimeType
    exact typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject
  · rcases habstractActive with
      ⟨_hnonObject, directives, bodySelectionSet, hmem, _hbodyNonempty,
        _hbodyNormal⟩
    rcases selectionSetNormal_inlineFragment_child_of_mem hnormal hmem with
      ⟨htypeObject, _hchildNormal⟩
    have hoverlap : schema.typesOverlap parentType runtimeType :=
      selectionSetValid_inlineFragment_some_typesOverlap_of_mem hvalid hmem
    exact typeIncludesObjectBool_of_typesOverlap_object schema hoverlap
      htypeObject

theorem selectionSetRuntimeActive_runtime_object_of_normal
    {schema : Schema} {parentType runtimeType : Name}
    {variableDefinitions : List VariableDefinition}
    {selectionSet : List Selection}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> selectionSetRuntimeActive schema parentType runtimeType selectionSet
      -> objectTypeNameBool schema runtimeType = true := by
  intro hschema hvalid hnormal hactive
  exact
    objectTypeNameBool_of_typeIncludesObjectBool hschema
      (selectionSetRuntimeActive_typeIncludes_of_normal hvalid hnormal
        hactive)

def fieldHeadProbeRuntimeCoherent
    (schema : Schema) (rootSelectionSet : List Selection)
    (parentType fieldName runtimeType : Name)
    (arguments : List Argument)
    (fieldDefinition : FieldDefinition)
    (childSelectionSet : List Selection)
    : Prop :=
  (objectTypeNameBool schema fieldDefinition.outputType.namedType = true
    ∧ runtimeType = fieldDefinition.outputType.namedType)
  ∨ ((TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema = true
      ∧ objectTypeNameBool schema fieldDefinition.outputType.namedType = false
      ∧ abstractRuntimeForFieldHeadDeep? schema parentType fieldName
          arguments parentType rootSelectionSet
        = some runtimeType
      ∧ selectionSetRuntimeActive schema fieldDefinition.outputType.namedType
          runtimeType childSelectionSet)

def selectionSetProbeRootCoherent
    (schema : Schema) (rootSelectionSet : List Selection)
    (parentType : Name) (selectionSet : List Selection)
    : Prop :=
  ∀ responseName fieldName arguments directives childSelectionSet fieldDefinition,
    Selection.field responseName fieldName arguments directives childSelectionSet
      ∈ selectionSet
    -> schema.lookupField parentType fieldName = some fieldDefinition
    -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema = true
    -> ∃ runtimeType,
        fieldHeadProbeRuntimeCoherent schema rootSelectionSet parentType
          fieldName runtimeType arguments fieldDefinition childSelectionSet

mutual
  inductive SelectionSetProbeRootCoherentDeep
      (schema : Schema) (rootSelectionSet : List Selection)
      : Name -> List Selection -> Prop where
    | nil {parentType : Name}
      : SelectionSetProbeRootCoherentDeep schema rootSelectionSet parentType []
    | cons {parentType : Name} {selection : Selection} {rest : List Selection}
      : SelectionProbeRootCoherentDeep schema rootSelectionSet parentType selection
        -> SelectionSetProbeRootCoherentDeep schema rootSelectionSet parentType rest
        -> SelectionSetProbeRootCoherentDeep schema rootSelectionSet parentType
            (selection :: rest)

  inductive SelectionProbeRootCoherentDeep
      (schema : Schema) (rootSelectionSet : List Selection)
      : Name -> Selection -> Prop where
    | field
      {parentType : Name}
      {responseName fieldName : Name}
      {arguments : List Argument}
      {directives : List DirectiveApplication}
      {childSelectionSet : List Selection}
      : (∀ fieldDefinition,
          schema.lookupField parentType fieldName = some fieldDefinition
          -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
              = true
          -> ∃ runtimeType,
              fieldHeadProbeRuntimeCoherent schema rootSelectionSet parentType
                fieldName runtimeType arguments fieldDefinition
                childSelectionSet)
        -> (∀ fieldDefinition,
              schema.lookupField parentType fieldName = some fieldDefinition
              -> SelectionSetProbeRootCoherentDeep schema rootSelectionSet
                  fieldDefinition.outputType.namedType childSelectionSet)
        -> SelectionProbeRootCoherentDeep schema rootSelectionSet parentType
            (Selection.field responseName fieldName arguments directives
              childSelectionSet)
    | inlineFragmentSome
      {parentType : Name}
      {typeCondition : Name}
      {directives : List DirectiveApplication}
      {childSelectionSet : List Selection}
      : SelectionSetProbeRootCoherentDeep schema rootSelectionSet
          typeCondition childSelectionSet
        -> SelectionProbeRootCoherentDeep schema rootSelectionSet parentType
            (Selection.inlineFragment (some typeCondition) directives childSelectionSet)
    | inlineFragmentNone
      {parentType : Name}
      {directives : List DirectiveApplication}
      {childSelectionSet : List Selection}
      : SelectionSetProbeRootCoherentDeep schema rootSelectionSet parentType
          childSelectionSet
        -> SelectionProbeRootCoherentDeep schema rootSelectionSet parentType
            (Selection.inlineFragment none directives childSelectionSet)
end

theorem SelectionSetProbeRootCoherentDeep.selection_of_mem
    {schema : Schema} {rootSelectionSet selectionSet : List Selection}
    {parentType : Name} {selection : Selection}
    : SelectionSetProbeRootCoherentDeep schema rootSelectionSet parentType selectionSet
      -> selection ∈ selectionSet
      -> SelectionProbeRootCoherentDeep schema rootSelectionSet parentType selection := by
  revert selection
  induction selectionSet with
  | nil =>
      intro selection hcoherent hmem
      cases hmem
  | cons head rest ih =>
      intro selection hcoherent hmem
      cases hcoherent with
      | cons hhead htail =>
          simp at hmem
          rcases hmem with hselection | hmem
          · subst selection
            exact hhead
          · exact ih htail hmem

theorem SelectionSetProbeRootCoherentDeep.field_head_of_mem
    {schema : Schema} {rootSelectionSet selectionSet : List Selection}
    {parentType responseName fieldName : Name}
    {arguments : List Argument} {directives : List DirectiveApplication}
    {childSelectionSet : List Selection} {fieldDefinition : FieldDefinition}
    : SelectionSetProbeRootCoherentDeep schema rootSelectionSet parentType selectionSet
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> ∃ runtimeType,
          fieldHeadProbeRuntimeCoherent schema rootSelectionSet parentType
            fieldName runtimeType arguments fieldDefinition childSelectionSet := by
  intro hcoherent hmem hlookup hcomposite
  have hselection :=
    hcoherent.selection_of_mem hmem
  cases hselection with
  | field hhead _hchild =>
      exact hhead fieldDefinition hlookup hcomposite

theorem SelectionSetProbeRootCoherentDeep.field_child_of_mem
    {schema : Schema} {rootSelectionSet selectionSet : List Selection}
    {parentType responseName fieldName : Name}
    {arguments : List Argument} {directives : List DirectiveApplication}
    {childSelectionSet : List Selection} {fieldDefinition : FieldDefinition}
    : SelectionSetProbeRootCoherentDeep schema rootSelectionSet parentType selectionSet
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> SelectionSetProbeRootCoherentDeep schema rootSelectionSet
          fieldDefinition.outputType.namedType childSelectionSet := by
  intro hcoherent hmem hlookup
  have hselection :=
    hcoherent.selection_of_mem hmem
  cases hselection with
  | field _hhead hchild =>
      exact hchild fieldDefinition hlookup

theorem SelectionSetProbeRootCoherentDeep.inlineFragment_some_child_of_mem
    {schema : Schema} {rootSelectionSet selectionSet : List Selection}
    {parentType typeCondition : Name}
    {directives : List DirectiveApplication}
    {childSelectionSet : List Selection}
    : SelectionSetProbeRootCoherentDeep schema rootSelectionSet parentType selectionSet
      -> Selection.inlineFragment (some typeCondition) directives childSelectionSet
          ∈ selectionSet
      -> SelectionSetProbeRootCoherentDeep schema rootSelectionSet
          typeCondition childSelectionSet := by
  intro hcoherent hmem
  have hselection :=
    hcoherent.selection_of_mem hmem
  cases hselection with
  | inlineFragmentSome hchild =>
      exact hchild

theorem SelectionSetProbeRootCoherentDeep.inlineFragment_none_child_of_mem
    {schema : Schema} {rootSelectionSet selectionSet : List Selection}
    {parentType : Name}
    {directives : List DirectiveApplication}
    {childSelectionSet : List Selection}
    : SelectionSetProbeRootCoherentDeep schema rootSelectionSet parentType selectionSet
      -> Selection.inlineFragment none directives childSelectionSet ∈ selectionSet
      -> SelectionSetProbeRootCoherentDeep schema rootSelectionSet parentType
          childSelectionSet := by
  intro hcoherent hmem
  have hselection :=
    hcoherent.selection_of_mem hmem
  cases hselection with
  | inlineFragmentNone hchild =>
      exact hchild

theorem selectionSetProbeRootCoherent_of_deep
    {schema : Schema} {rootSelectionSet selectionSet : List Selection}
    {parentType : Name}
    : SelectionSetProbeRootCoherentDeep schema rootSelectionSet parentType selectionSet
      -> selectionSetProbeRootCoherent schema rootSelectionSet parentType
          selectionSet := by
  intro hdeep responseName fieldName arguments directives childSelectionSet
    fieldDefinition hmem hlookup hcomposite
  exact
    hdeep.field_head_of_mem hmem hlookup hcomposite

theorem fieldHeadProbeRuntimeCoherent_typeIncludes_of_child_normal
    {schema : Schema} {rootSelectionSet childSelectionSet : List Selection}
    {parentType fieldName runtimeType : Name}
    {variableDefinitions : List VariableDefinition}
    {arguments : List Argument} {fieldDefinition : FieldDefinition}
    : Validation.selectionSetValid schema variableDefinitions
        fieldDefinition.outputType.namedType childSelectionSet
      -> selectionSetNormal schema fieldDefinition.outputType.namedType childSelectionSet
      -> fieldHeadProbeRuntimeCoherent schema rootSelectionSet parentType
          fieldName runtimeType arguments fieldDefinition childSelectionSet
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType runtimeType
          = true := by
  intro hchildValid hchildNormal hcoherent
  rcases hcoherent with hobject | habstract
  · rcases hobject with ⟨hobject, hruntime⟩
    subst runtimeType
    exact typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject
  · exact
      selectionSetRuntimeActive_typeIncludes_of_normal hchildValid
        hchildNormal
        habstract.2.2.2

theorem selectionSetRuntimeActive_of_fieldHeadProbeRuntimeCoherent
    {schema : Schema} {rootSelectionSet childSelectionSet : List Selection}
    {parentType fieldName runtimeType : Name}
    {arguments : List Argument} {fieldDefinition : FieldDefinition}
    : fieldHeadProbeRuntimeCoherent schema rootSelectionSet parentType
        fieldName runtimeType arguments fieldDefinition childSelectionSet
      -> selectionSetRuntimeActive schema fieldDefinition.outputType.namedType
          runtimeType childSelectionSet := by
  intro hcoherent
  rcases hcoherent with hobject | habstract
  · rcases hobject with ⟨hobject, hruntime⟩
    subst runtimeType
    exact selectionSetRuntimeActive_object hobject
  · exact habstract.2.2.2

theorem fieldHeadProbeRuntimeCoherent_runtime_object_of_child_normal
    {schema : Schema} {rootSelectionSet childSelectionSet : List Selection}
    {parentType fieldName runtimeType : Name}
    {variableDefinitions : List VariableDefinition}
    {arguments : List Argument} {fieldDefinition : FieldDefinition}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema variableDefinitions
          fieldDefinition.outputType.namedType childSelectionSet
      -> selectionSetNormal schema fieldDefinition.outputType.namedType childSelectionSet
      -> fieldHeadProbeRuntimeCoherent schema rootSelectionSet parentType
          fieldName runtimeType arguments fieldDefinition childSelectionSet
      -> objectTypeNameBool schema runtimeType = true := by
  intro hschema hchildValid hchildNormal hcoherent
  exact
    objectTypeNameBool_of_typeIncludesObjectBool hschema
      (fieldHeadProbeRuntimeCoherent_typeIncludes_of_child_normal
        hchildValid hchildNormal hcoherent)

theorem SelectionSetProbeRootCoherentDeep.field_child_runtimeActive_of_mem
    {schema : Schema} {rootSelectionSet selectionSet childSelectionSet : List Selection}
    {parentType responseName fieldName : Name}
    {arguments : List Argument} {directives : List DirectiveApplication}
    {variableDefinitions : List VariableDefinition}
    {fieldDefinition : FieldDefinition}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema variableDefinitions
          fieldDefinition.outputType.namedType childSelectionSet
      -> selectionSetNormal schema fieldDefinition.outputType.namedType childSelectionSet
      -> SelectionSetProbeRootCoherentDeep schema rootSelectionSet parentType selectionSet
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> ∃ runtimeType,
          fieldHeadProbeRuntimeCoherent schema rootSelectionSet parentType
            fieldName runtimeType arguments fieldDefinition childSelectionSet
          ∧ schema.typeIncludesObjectBool fieldDefinition.outputType.namedType runtimeType
            = true
          ∧ objectTypeNameBool schema runtimeType = true
          ∧ selectionSetRuntimeActive schema
              fieldDefinition.outputType.namedType runtimeType childSelectionSet
          ∧ SelectionSetProbeRootCoherentDeep schema rootSelectionSet
              fieldDefinition.outputType.namedType childSelectionSet := by
  intro hschema hchildValid hchildNormal hcoherent hmem hlookup hcomposite
  rcases hcoherent.field_head_of_mem hmem hlookup hcomposite with
    ⟨runtimeType, hhead⟩
  have hinclude :
      schema.typeIncludesObjectBool fieldDefinition.outputType.namedType
        runtimeType = true :=
    fieldHeadProbeRuntimeCoherent_typeIncludes_of_child_normal hchildValid
      hchildNormal hhead
  have hruntimeObject : objectTypeNameBool schema runtimeType = true :=
    objectTypeNameBool_of_typeIncludesObjectBool hschema hinclude
  have hactive :
      selectionSetRuntimeActive schema fieldDefinition.outputType.namedType
        runtimeType childSelectionSet :=
    selectionSetRuntimeActive_of_fieldHeadProbeRuntimeCoherent hhead
  have hchildCoherent :
      SelectionSetProbeRootCoherentDeep schema rootSelectionSet
        fieldDefinition.outputType.namedType childSelectionSet :=
    hcoherent.field_child_of_mem hmem hlookup
  exact
    ⟨runtimeType, hhead, hinclude, hruntimeObject, hactive,
      hchildCoherent⟩

theorem fieldHeadProbeRuntimeCoherent.to_compositeTargetRuntime
    {schema : Schema} {rootSelectionSet childSelectionSet : List Selection}
    {parentType fieldName runtimeType : Name}
    {arguments : List Argument} {fieldDefinition : FieldDefinition}
    : fieldHeadProbeRuntimeCoherent schema rootSelectionSet parentType
        fieldName runtimeType arguments fieldDefinition childSelectionSet
      -> ((objectTypeNameBool schema fieldDefinition.outputType.namedType = true
            ∧ runtimeType = fieldDefinition.outputType.namedType)
          ∨ ((TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
                = true
              ∧ objectTypeNameBool schema fieldDefinition.outputType.namedType = false
              ∧ abstractRuntimeForFieldHeadDeep? schema parentType fieldName
                  arguments parentType rootSelectionSet
                = some runtimeType)) := by
  intro hcoherent
  rcases hcoherent with hobject | habstract
  · exact Or.inl hobject
  · exact Or.inr ⟨habstract.1, habstract.2.1, habstract.2.2.1⟩

end GroundTypeNormalization

end NormalForm

end GraphQL
