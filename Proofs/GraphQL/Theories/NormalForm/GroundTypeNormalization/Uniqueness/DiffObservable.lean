import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.ObservablePath
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.TaggedObservable

/-!
Diff-guided observable support for normal-form uniqueness.

The existing tagged probe lemmas require a promotion hypothesis that relates
abstract runtime choices made in a focused selection set to the root selection set
used by the probe resolvers.  This module names that hypothesis and proves the
small child-projection lemmas needed when following a syntactic diff into a field
or inline-fragment body.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

def selectionSetDeepPromotionAvailable
    (schema : Schema) (rootSelectionSet : List Selection)
    (parentType : Name) (selectionSet : List Selection)
    : Prop :=
  ∀ abstractTargetParent abstractTargetField targetRuntimeType targetFieldDefinition,
    schema.lookupField abstractTargetParent abstractTargetField
      = some targetFieldDefinition
    -> (TypeRef.named targetFieldDefinition.outputType.namedType).isCompositeBool schema
        = true
    -> objectTypeNameBool schema targetFieldDefinition.outputType.namedType = false
    -> abstractRuntimeForFieldDeep? schema abstractTargetParent
          abstractTargetField parentType selectionSet
        = some targetRuntimeType
    -> ∃ runtimeType,
        abstractRuntimeForFieldDeep? schema abstractTargetParent
            abstractTargetField abstractTargetParent rootSelectionSet
          = some runtimeType
        ∧ schema.typeIncludesObjectBool
            targetFieldDefinition.outputType.namedType runtimeType
          = true

def selectionSetDeepPromotionPreservesRuntime
    (schema : Schema) (rootSelectionSet : List Selection)
    (parentType : Name) (selectionSet : List Selection)
    : Prop :=
  ∀ abstractTargetParent abstractTargetField targetRuntimeType targetFieldDefinition,
    schema.lookupField abstractTargetParent abstractTargetField
      = some targetFieldDefinition
    -> (TypeRef.named targetFieldDefinition.outputType.namedType).isCompositeBool schema
        = true
    -> objectTypeNameBool schema targetFieldDefinition.outputType.namedType = false
    -> abstractRuntimeForFieldDeep? schema abstractTargetParent
          abstractTargetField parentType selectionSet
        = some targetRuntimeType
    -> abstractRuntimeForFieldDeep? schema abstractTargetParent
          abstractTargetField abstractTargetParent rootSelectionSet
        = some targetRuntimeType

def selectionSetDeepHeadPromotionPreservesRuntime
    (schema : Schema) (rootSelectionSet : List Selection)
    (parentType : Name) (selectionSet : List Selection)
    : Prop :=
  ∀ abstractTargetParent abstractTargetField targetArguments
    targetRuntimeType targetFieldDefinition,
    schema.lookupField abstractTargetParent abstractTargetField
      = some targetFieldDefinition
    -> (TypeRef.named targetFieldDefinition.outputType.namedType).isCompositeBool schema
        = true
    -> objectTypeNameBool schema targetFieldDefinition.outputType.namedType = false
    -> abstractRuntimeForFieldHeadDeep? schema abstractTargetParent
          abstractTargetField targetArguments parentType selectionSet
        = some targetRuntimeType
    -> abstractRuntimeForFieldHeadDeep? schema abstractTargetParent
          abstractTargetField targetArguments abstractTargetParent
          rootSelectionSet
        = some targetRuntimeType

theorem selectionSetDeepPromotionAvailable_of_preservesRuntime
    {schema : Schema} {rootSelectionSet : List Selection}
    {variableDefinitions : List VariableDefinition}
    {parentType : Name} {selectionSet : List Selection}
    : Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> selectionSetDirectiveFree selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> selectionSetDeepPromotionPreservesRuntime schema rootSelectionSet
          parentType selectionSet
      -> selectionSetDeepPromotionAvailable schema rootSelectionSet parentType
          selectionSet := by
  intro hvalid hfree hnormal hpreserve abstractTargetParent
    abstractTargetField targetRuntimeType targetFieldDefinition htargetLookup
    htargetComposite htargetNonObject hlocalRuntime
  exact
    ⟨targetRuntimeType,
      hpreserve abstractTargetParent abstractTargetField targetRuntimeType
        targetFieldDefinition htargetLookup htargetComposite
        htargetNonObject hlocalRuntime,
      abstractRuntimeForFieldDeep?_some_include_of_valid_normal hvalid hfree
        hnormal htargetLookup htargetComposite htargetNonObject
        hlocalRuntime⟩

theorem selectionSetDeepHeadPromotionAvailable_of_preservesRuntime
    {schema : Schema} {rootSelectionSet : List Selection}
    {variableDefinitions : List VariableDefinition}
    {parentType : Name} {selectionSet : List Selection}
    : Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> selectionSetDirectiveFree selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> selectionSetDeepHeadPromotionPreservesRuntime schema rootSelectionSet
          parentType selectionSet
      -> selectionSetDeepHeadPromotionAvailable schema rootSelectionSet parentType
          selectionSet := by
  intro hvalid hfree hnormal hpreserve abstractTargetParent
    abstractTargetField targetArguments targetRuntimeType targetFieldDefinition
    htargetLookup htargetComposite htargetNonObject hlocalRuntime
  exact
    ⟨targetRuntimeType,
      hpreserve abstractTargetParent abstractTargetField targetArguments
        targetRuntimeType targetFieldDefinition htargetLookup
        htargetComposite htargetNonObject hlocalRuntime,
      abstractRuntimeForFieldHeadDeep?_some_include_of_valid_normal hvalid
        hfree hnormal htargetLookup htargetComposite htargetNonObject
        hlocalRuntime⟩

theorem abstractRuntimeForFieldHeadDeep?_framed_exact
    {schema : Schema}
    {currentParent targetParent targetField runtimeType : Name}
    {targetArguments : List Argument}
    {selectionSet : List Selection}
    : abstractRuntimeForFieldHeadDeep? schema targetParent targetField
          targetArguments currentParent selectionSet
        = some runtimeType
      -> abstractRuntimeForFieldHeadDeep? schema targetParent targetField
            targetArguments targetParent
            [Selection.inlineFragment (some currentParent) [] selectionSet]
          = some runtimeType := by
  intro hruntime
  simp [abstractRuntimeForFieldHeadDeep?, hruntime]

theorem abstractRuntimeForFieldDeep?_framed_exact
    {schema : Schema}
    {currentParent targetParent targetField runtimeType : Name}
    {selectionSet : List Selection}
    : abstractRuntimeForFieldDeep? schema targetParent targetField currentParent
          selectionSet
        = some runtimeType
      -> abstractRuntimeForFieldDeep? schema targetParent targetField targetParent
            [Selection.inlineFragment (some currentParent) [] selectionSet]
          = some runtimeType := by
  intro hruntime
  simp [abstractRuntimeForFieldDeep?, hruntime]

theorem abstractRuntimeForFieldDeep?_framed_singleton_field_firstInline
    {schema : Schema}
    {parentType responseName fieldName runtimeType : Name}
    {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet : List Selection}
    : firstInlineFragmentTypeCondition? childSelectionSet = some runtimeType
      -> abstractRuntimeForFieldDeep? schema parentType fieldName parentType
            [Selection.inlineFragment (some parentType) []
              [Selection.field responseName fieldName arguments directives
                childSelectionSet]]
          = some runtimeType := by
  intro hfirst
  simp [abstractRuntimeForFieldDeep?, hfirst]

theorem selectionSetDeepPromotionAvailable_single_framed
    {schema : Schema}
    {variableDefinitions : List VariableDefinition}
    {parentType : Name} {selectionSet : List Selection}
    : Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> selectionSetDirectiveFree selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> selectionSetDeepPromotionAvailable schema
          [Selection.inlineFragment (some parentType) [] selectionSet]
          parentType selectionSet := by
  intro hvalid hfree hnormal
  intro abstractTargetParent abstractTargetField targetRuntimeType
    targetFieldDefinition htargetLookup htargetComposite htargetNonObject
    hlocalRuntime
  exact
    ⟨targetRuntimeType,
      abstractRuntimeForFieldDeep?_framed_exact hlocalRuntime,
      abstractRuntimeForFieldDeep?_some_include_of_valid_normal hvalid hfree
        hnormal htargetLookup htargetComposite htargetNonObject
        hlocalRuntime⟩

theorem selectionSetDeepPromotionPreservesRuntime_single_framed
    {schema : Schema}
    {parentType : Name} {selectionSet : List Selection}
    : selectionSetDeepPromotionPreservesRuntime schema
        [Selection.inlineFragment (some parentType) [] selectionSet]
        parentType selectionSet := by
  intro _abstractTargetParent _abstractTargetField _targetRuntimeType
    _targetFieldDefinition _htargetLookup _htargetComposite
    _htargetNonObject hlocalRuntime
  exact abstractRuntimeForFieldDeep?_framed_exact hlocalRuntime

theorem selectionSetDeepHeadPromotionPreservesRuntime_single_framed
    {schema : Schema}
    {parentType : Name} {selectionSet : List Selection}
    : selectionSetDeepHeadPromotionPreservesRuntime schema
        [Selection.inlineFragment (some parentType) [] selectionSet]
        parentType selectionSet := by
  intro _abstractTargetParent _abstractTargetField _targetArguments
    _targetRuntimeType _targetFieldDefinition _htargetLookup
    _htargetComposite _htargetNonObject hlocalRuntime
  exact abstractRuntimeForFieldHeadDeep?_framed_exact hlocalRuntime

theorem selectionSetDeepHeadPromotionAvailable_single_framed
    {schema : Schema}
    {variableDefinitions : List VariableDefinition}
    {parentType : Name} {selectionSet : List Selection}
    : Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> selectionSetDirectiveFree selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> selectionSetDeepHeadPromotionAvailable schema
          [Selection.inlineFragment (some parentType) [] selectionSet]
          parentType selectionSet := by
  intro hvalid hfree hnormal
  exact
    selectionSetDeepHeadPromotionAvailable_of_preservesRuntime hvalid hfree
      hnormal selectionSetDeepHeadPromotionPreservesRuntime_single_framed

theorem selectionSetDeepPromotionAvailable_field_child_of_mem
    {schema : Schema} {rootSelectionSet : List Selection}
    {variableDefinitions : List VariableDefinition}
    {parentType responseName fieldName : Name}
    {arguments : List Argument} {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    : Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> selectionSetDirectiveFree selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> selectionSetDeepPromotionAvailable schema rootSelectionSet parentType
          selectionSet
      -> selectionSetDeepPromotionAvailable schema rootSelectionSet
          fieldDefinition.outputType.namedType childSelectionSet := by
  intro hvalid hfree hnormal hmem hlookup hpromote
  intro abstractTargetParent abstractTargetField targetRuntimeType
    targetFieldDefinition htargetLookup htargetComposite htargetNonObject
    hlocalRuntime
  rcases
      abstractRuntimeForFieldDeep?_object_field_child_promote_some_of_valid_normal
        hvalid hfree hnormal hmem hlookup htargetLookup htargetComposite
        htargetNonObject hlocalRuntime with
    ⟨parentRuntimeType, hparentRuntime, _hparentInclude⟩
  exact
    hpromote abstractTargetParent abstractTargetField parentRuntimeType
      targetFieldDefinition htargetLookup htargetComposite htargetNonObject
      hparentRuntime

theorem selectionSetDeepPromotionAvailable_inlineFragment_child_of_mem
    {schema : Schema} {rootSelectionSet : List Selection}
    {variableDefinitions : List VariableDefinition}
    {parentType typeCondition : Name}
    {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    : Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> selectionSetDirectiveFree selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> Selection.inlineFragment (some typeCondition) directives childSelectionSet
          ∈ selectionSet
      -> selectionSetDeepPromotionAvailable schema rootSelectionSet parentType
          selectionSet
      -> selectionSetDeepPromotionAvailable schema rootSelectionSet typeCondition
          childSelectionSet := by
  intro hvalid hfree hnormal hmem hpromote
  intro abstractTargetParent abstractTargetField targetRuntimeType
    targetFieldDefinition htargetLookup htargetComposite htargetNonObject
    hlocalRuntime
  rcases
      abstractRuntimeForFieldDeep?_inlineFragment_child_promote_some_of_valid_normal
        hvalid hfree hnormal hmem htargetLookup htargetComposite
        htargetNonObject hlocalRuntime with
    ⟨parentRuntimeType, hparentRuntime, _hparentInclude⟩
  exact
    hpromote abstractTargetParent abstractTargetField parentRuntimeType
      targetFieldDefinition htargetLookup htargetComposite htargetNonObject
      hparentRuntime

theorem selectionSetDeepHeadPromotionAvailable_field_child_of_mem
    {schema : Schema} {rootSelectionSet : List Selection}
    {variableDefinitions : List VariableDefinition}
    {parentType responseName fieldName : Name}
    {arguments : List Argument} {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    : Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> selectionSetDirectiveFree selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> selectionSetDeepHeadPromotionAvailable schema rootSelectionSet parentType
          selectionSet
      -> selectionSetDeepHeadPromotionAvailable schema rootSelectionSet
          fieldDefinition.outputType.namedType childSelectionSet := by
  intro hvalid hfree hnormal hmem hlookup hpromote
  intro abstractTargetParent abstractTargetField targetArguments
    targetRuntimeType targetFieldDefinition htargetLookup htargetComposite
    htargetNonObject hlocalRuntime
  rcases
      abstractRuntimeForFieldHeadDeep?_object_field_child_promote_some_of_valid_normal
        hvalid hfree hnormal hmem hlookup hlocalRuntime with
    ⟨parentRuntimeType, hparentRuntime⟩
  exact
    hpromote abstractTargetParent abstractTargetField targetArguments
      parentRuntimeType targetFieldDefinition htargetLookup htargetComposite
      htargetNonObject hparentRuntime

theorem selectionSetDeepHeadPromotionAvailable_inlineFragment_child_of_mem
    {schema : Schema} {rootSelectionSet : List Selection}
    {variableDefinitions : List VariableDefinition}
    {parentType typeCondition : Name}
    {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    : Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> selectionSetDirectiveFree selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> Selection.inlineFragment (some typeCondition) directives childSelectionSet
          ∈ selectionSet
      -> selectionSetDeepHeadPromotionAvailable schema rootSelectionSet parentType
          selectionSet
      -> selectionSetDeepHeadPromotionAvailable schema rootSelectionSet
          typeCondition childSelectionSet := by
  intro hvalid hfree hnormal hmem hpromote
  intro abstractTargetParent abstractTargetField targetArguments
    targetRuntimeType targetFieldDefinition htargetLookup htargetComposite
    htargetNonObject hlocalRuntime
  rcases
      abstractRuntimeForFieldHeadDeep?_inlineFragment_child_promote_some_of_valid_normal
        hvalid hfree hnormal hmem hlocalRuntime with
    ⟨parentRuntimeType, hparentRuntime⟩
  exact
    hpromote abstractTargetParent abstractTargetField targetArguments
      parentRuntimeType targetFieldDefinition htargetLookup htargetComposite
      htargetNonObject hparentRuntime

theorem selectionSet_nonempty_of_normalSelectionSetObservableLeaf
    {schema : Schema} {parentType : Name} {selectionSet : List Selection}
    : NormalSelectionSetObservableLeaf schema parentType selectionSet
      -> selectionSet ≠ [] := by
  intro hobservable hempty
  cases hobservable with
  | objectLeaf _hobject hmem _hlookup _hleaf =>
      subst selectionSet
      simp at hmem
  | objectChild _hobject hmem _hlookup _hcomposite _hchild =>
      subst selectionSet
      simp at hmem
  | abstractInlineFragment _hnonObject hmem _hchild =>
      subst selectionSet
      simp at hmem

theorem typeRef_named_isCompositeBool_of_isCompositeType
    {schema : Schema} {typeName : Name}
    : schema.isCompositeType typeName
      -> (TypeRef.named typeName).isCompositeBool schema = true := by
  intro hcomposite
  unfold Schema.isCompositeType at hcomposite
  unfold TypeRef.isCompositeBool TypeRef.namedType
  rcases hcomposite with ⟨typeDefinition, hlookup, htypeComposite⟩
  rw [hlookup]
  cases typeDefinition <;> simp [TypeDefinition.isCompositeType] at htypeComposite ⊢

inductive NormalSelectionSetObservableLeafAtRuntime (schema : Schema)
    : Name -> Name -> List Selection -> Prop where
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
      -> NormalSelectionSetObservableLeafAtRuntime schema parentType parentType
          selectionSet
  | objectChild
    {parentType childRuntimeType responseName fieldName : Name}
    {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    : objectTypeNameBool schema parentType = true
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> schema.isCompositeType fieldDefinition.outputType.namedType
      -> NormalSelectionSetObservableLeafAtRuntime schema
          fieldDefinition.outputType.namedType childRuntimeType
          childSelectionSet
      -> ((objectTypeNameBool schema fieldDefinition.outputType.namedType = true
            ∧ childRuntimeType = fieldDefinition.outputType.namedType)
          ∨ ((TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
                = true
              ∧ objectTypeNameBool schema fieldDefinition.outputType.namedType = false
              ∧ abstractRuntimeForFieldDeep? schema parentType fieldName
                  parentType selectionSet
                = some childRuntimeType))
      -> NormalSelectionSetObservableLeafAtRuntime schema parentType parentType
          selectionSet
  | abstractInlineFragment
    {parentType typeCondition childRuntimeType : Name}
    {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    : objectTypeNameBool schema parentType = false
      -> objectTypeNameBool schema typeCondition = true
      -> schema.typeIncludesObjectBool parentType typeCondition = true
      -> firstInlineFragmentTypeCondition? selectionSet = some typeCondition
      -> Selection.inlineFragment (some typeCondition) directives childSelectionSet
          ∈ selectionSet
      -> NormalSelectionSetObservableLeafAtRuntime schema typeCondition
          childRuntimeType childSelectionSet
      -> NormalSelectionSetObservableLeafAtRuntime schema parentType
          typeCondition selectionSet

theorem normalSelectionSetObservableLeafAtRuntime_runtime_eq_of_object_core
    {schema : Schema} {parentType runtimeType : Name}
    {selectionSet : List Selection}
    : objectTypeNameBool schema parentType = true
      -> NormalSelectionSetObservableLeafAtRuntime schema parentType runtimeType
          selectionSet
      -> runtimeType = parentType := by
  intro hobject hobservable
  cases hobservable with
  | objectLeaf =>
      rfl
  | objectChild =>
      rfl
  | abstractInlineFragment hnonObject _htypeObject _hinclude _hfirst _hmem
      _hchild =>
      rw [hobject] at hnonObject
      simp at hnonObject

theorem normalSelectionSetObservableLeafAtRuntime_firstInline_of_abstract_core
    {schema : Schema} {parentType runtimeType : Name}
    {selectionSet : List Selection}
    : objectTypeNameBool schema parentType = false
      -> NormalSelectionSetObservableLeafAtRuntime schema parentType runtimeType
          selectionSet
      -> firstInlineFragmentTypeCondition? selectionSet = some runtimeType := by
  intro hnonObject hobservable
  cases hobservable with
  | objectLeaf hobject _hmem _hlookup _hleaf =>
      rw [hnonObject] at hobject
      simp at hobject
  | objectChild hobject _hmem _hlookup _hcomposite _hchild _hruntime =>
      rw [hnonObject] at hobject
      simp at hobject
  | abstractInlineFragment _hnonObject _htypeObject _hinclude hfirst _hmem
      _hchild =>
      exact hfirst

theorem normalSelectionSetObservableLeafAtRuntime_of_valid_normal_nonempty
    (schema : Schema)
    : ∀ parentType variableDefinitions (selectionSet : List Selection),
        Validation.selectionSetValid schema variableDefinitions parentType selectionSet
        -> selectionSetNormal schema parentType selectionSet
        -> selectionSet ≠ []
        -> ∃ runtimeType,
            NormalSelectionSetObservableLeafAtRuntime schema parentType
              runtimeType selectionSet
  | parentType, variableDefinitions, selectionSet, hvalid, hnormal,
      hnonempty => by
      by_cases hparentObject : objectTypeNameBool schema parentType = true
      · cases selectionSet with
        | nil =>
            exact False.elim (hnonempty rfl)
        | cons selection rest =>
        have hallFields :
            selectionsAllFields (selection :: rest) :=
          selectionSetNormal_allFields_of_object hnormal hparentObject
        have hselectionField : Selection.isField selection :=
          hallFields selection (by simp)
        cases selection with
        | inlineFragment typeCondition directives childSelectionSet =>
            simp [Selection.isField] at hselectionField
        | field responseName fieldName arguments directives childSelectionSet =>
        have hmem :
            Selection.field responseName fieldName arguments directives
                childSelectionSet ∈
              Selection.field responseName fieldName arguments directives
                childSelectionSet :: rest := by
          simp
        rcases
          selectionSetValid_field_lookup_leaf_or_composite_child hvalid
            hmem with
          ⟨fieldDefinition, hlookup, hkind⟩
        rcases hkind with hleaf | hcomposite
        · exact
            ⟨parentType,
              NormalSelectionSetObservableLeafAtRuntime.objectLeaf
                hparentObject hmem hlookup hleaf.1⟩
        · have hchildNormal :
              selectionSetNormal schema fieldDefinition.outputType.namedType
                childSelectionSet :=
            selectionSetNormal_field_child_of_mem_lookup hnormal hmem
              hlookup
          have hchildSize :
              SelectionSet.size childSelectionSet <
                SelectionSet.size
                  (Selection.field responseName fieldName arguments
                    directives childSelectionSet :: rest) :=
            selectionSet_size_field_child_lt_of_mem hmem
          rcases
              normalSelectionSetObservableLeafAtRuntime_of_valid_normal_nonempty
                schema fieldDefinition.outputType.namedType
                variableDefinitions childSelectionSet hcomposite.2.2
                hchildNormal hcomposite.2.1 with
            ⟨childRuntimeType, hchildObservable⟩
          have hruntime :
              ((objectTypeNameBool schema
                    fieldDefinition.outputType.namedType = true
                  ∧ childRuntimeType =
                    fieldDefinition.outputType.namedType)
                ∨
                ((TypeRef.named
                    fieldDefinition.outputType.namedType).isCompositeBool
                    schema = true
                  ∧ objectTypeNameBool schema
                    fieldDefinition.outputType.namedType = false
                  ∧ abstractRuntimeForFieldDeep? schema parentType fieldName
                    parentType
                    (Selection.field responseName fieldName arguments
                      directives childSelectionSet :: rest) =
                    some childRuntimeType)) := by
            by_cases hreturnObject :
                objectTypeNameBool schema
                    fieldDefinition.outputType.namedType = true
            · have hchildRuntime :
                  childRuntimeType =
                    fieldDefinition.outputType.namedType :=
                normalSelectionSetObservableLeafAtRuntime_runtime_eq_of_object_core
                  hreturnObject hchildObservable
              exact Or.inl ⟨hreturnObject, hchildRuntime⟩
            · have hreturnNonObject :
                  objectTypeNameBool schema
                      fieldDefinition.outputType.namedType = false := by
                cases h :
                    objectTypeNameBool schema
                      fieldDefinition.outputType.namedType
                · rfl
                · exact False.elim (hreturnObject h)
              have hfirst :
                  firstInlineFragmentTypeCondition? childSelectionSet =
                    some childRuntimeType :=
                normalSelectionSetObservableLeafAtRuntime_firstInline_of_abstract_core
                  hreturnNonObject hchildObservable
              have hcompositeBool :
                  (TypeRef.named
                    fieldDefinition.outputType.namedType).isCompositeBool
                    schema = true :=
                typeRef_named_isCompositeBool_of_isCompositeType hcomposite.1
              exact Or.inr
                ⟨hcompositeBool, hreturnNonObject,
                  by simp [abstractRuntimeForFieldDeep?, hfirst]⟩
          exact
            ⟨parentType,
              NormalSelectionSetObservableLeafAtRuntime.objectChild
                hparentObject hmem hlookup hcomposite.1 hchildObservable
                hruntime⟩
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
              ⟨htypeObject, hchildNormal⟩
            have htypeObjectBool :
                objectTypeNameBool schema typeCondition = true :=
              objectTypeNameBool_eq_true_of_objectType_forNormality schema
                htypeObject
            have hchildValid :
                Validation.selectionSetValid schema variableDefinitions
                  typeCondition childSelectionSet :=
              selectionSetValid_inlineFragment_some_child_of_mem hvalid
                hmem
            have hoverlap : schema.typesOverlap parentType typeCondition :=
              selectionSetValid_inlineFragment_some_typesOverlap_of_mem hvalid
                hmem
            have hinclude :
                schema.typeIncludesObjectBool parentType typeCondition =
                  true :=
              typeIncludesObjectBool_of_typesOverlap_object schema hoverlap
                htypeObject
            have hchildSize :
                SelectionSet.size childSelectionSet <
                  SelectionSet.size
                    (Selection.inlineFragment (some typeCondition) directives
                      childSelectionSet :: rest) :=
              selectionSet_size_inlineFragment_child_lt_of_mem hmem
            rcases
              normalSelectionSetObservableLeafAtRuntime_of_valid_normal_nonempty
                schema typeCondition variableDefinitions childSelectionSet
                hchildValid hchildNormal
                (selectionSetValid_inlineFragment_some_child_nonempty_of_mem
                  hvalid hmem) with
            ⟨childRuntimeType, hchildObservable⟩
            exact
              ⟨typeCondition,
                NormalSelectionSetObservableLeafAtRuntime.abstractInlineFragment
                  hparentAbstract htypeObjectBool hinclude
                  (by simp [firstInlineFragmentTypeCondition?]) hmem
                  hchildObservable⟩
termination_by _parentType _variableDefinitions selectionSet =>
  SelectionSet.size selectionSet
decreasing_by
  all_goals
    simp_wf
    first
    | exact hchildSize
    | simp_all

theorem normalSelectionSetObservableLeafAtRuntime_runtime_eq_of_object
    {schema : Schema} {parentType runtimeType : Name}
    {selectionSet : List Selection}
    : objectTypeNameBool schema parentType = true
      -> NormalSelectionSetObservableLeafAtRuntime schema parentType runtimeType
          selectionSet
      -> runtimeType = parentType := by
  intro hobject hobservable
  cases hobservable with
  | objectLeaf =>
      rfl
  | objectChild =>
      rfl
  | abstractInlineFragment hnonObject _htypeObject _hinclude _hmem _hchild =>
      rw [hobject] at hnonObject
      simp at hnonObject

theorem normalSelectionSetObservableLeafAtRuntime_typeIncludes
    {schema : Schema} {parentType runtimeType : Name}
    {selectionSet : List Selection}
    : NormalSelectionSetObservableLeafAtRuntime schema parentType runtimeType selectionSet
      -> schema.typeIncludesObjectBool parentType runtimeType = true := by
  intro hobservable
  cases hobservable with
  | objectLeaf hobject _hmem _hlookup _hleaf =>
      exact typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject
  | objectChild hobject _hmem _hlookup _hcomposite _hchild =>
      exact typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject
  | abstractInlineFragment _hnonObject _htypeObject hinclude _hfirst _hmem
      _hchild =>
      exact hinclude

theorem normalSelectionSetObservableLeafAtRuntime_firstInline_of_abstract
    {schema : Schema} {parentType runtimeType : Name}
    {selectionSet : List Selection}
    : objectTypeNameBool schema parentType = false
      -> NormalSelectionSetObservableLeafAtRuntime schema parentType runtimeType
          selectionSet
      -> firstInlineFragmentTypeCondition? selectionSet = some runtimeType := by
  intro hnonObject hobservable
  cases hobservable with
  | objectLeaf hobject _hmem _hlookup _hleaf =>
      rw [hnonObject] at hobject
      simp at hobject
  | objectChild hobject _hmem _hlookup _hcomposite _hchild =>
      rw [hnonObject] at hobject
      simp at hobject
  | abstractInlineFragment _hnonObject _htypeObject _hinclude hfirst _hmem
      _hchild =>
      exact hfirst

theorem selectionSet_nonempty_of_normalSelectionSetObservableLeafAtRuntime
    {schema : Schema} {parentType runtimeType : Name}
    {selectionSet : List Selection}
    : NormalSelectionSetObservableLeafAtRuntime schema parentType runtimeType selectionSet
      -> selectionSet ≠ [] := by
  intro hobservable hempty
  cases hobservable with
  | objectLeaf _hobject hmem _hlookup _hleaf =>
      subst selectionSet
      simp at hmem
  | objectChild _hobject hmem _hlookup _hcomposite _hchild _hruntime =>
      subst selectionSet
      simp at hmem
  | abstractInlineFragment _hnonObject _htypeObject _hinclude _hfirst hmem
      _hchild =>
      subst selectionSet
      simp at hmem

theorem inlineFragment_child_valid_free_normal_assumptions
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType typeCondition : Name}
    {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    : Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> selectionSetDirectiveFree selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> Selection.inlineFragment (some typeCondition) directives childSelectionSet
          ∈ selectionSet
      -> Validation.selectionSetValid schema variableDefinitions typeCondition
            childSelectionSet
          ∧ selectionSetDirectiveFree childSelectionSet
          ∧ schema.objectType typeCondition
          ∧ schema.typeIncludesObjectBool parentType typeCondition = true
          ∧ childSelectionSet ≠ []
          ∧ selectionSetNormal schema typeCondition childSelectionSet := by
  intro hvalid hfree hnormal hmem
  have hchildValid :
      Validation.selectionSetValid schema variableDefinitions typeCondition
        childSelectionSet :=
    selectionSetValid_inlineFragment_some_child_of_mem hvalid hmem
  have hchildFree :
      selectionSetDirectiveFree childSelectionSet :=
    selectionSetDirectiveFree_inlineFragment_child_of_mem hfree hmem
  rcases selectionSetNormal_inlineFragment_child_of_mem hnormal hmem with
    ⟨htypeObject, hchildNormal⟩
  have hoverlap : schema.typesOverlap parentType typeCondition :=
    selectionSetValid_inlineFragment_some_typesOverlap_of_mem hvalid hmem
  have hinclude :
      schema.typeIncludesObjectBool parentType typeCondition = true :=
    typeIncludesObjectBool_of_typesOverlap_object schema hoverlap htypeObject
  exact
    ⟨hchildValid, hchildFree, htypeObject, hinclude,
      selectionSetValid_inlineFragment_some_child_nonempty_of_mem hvalid hmem,
      hchildNormal⟩

end GroundTypeNormalization

end NormalForm

end GraphQL
