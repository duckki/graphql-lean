import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.FocusedPathProbePathLocalCompositeSeparation

/-!
Selected-runtime spines, resolver references, and field execution for focused probes.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

inductive PathLocalSelectionSetObservableLeafAtRuntime (schema : Schema)
    : Name -> Name -> List Selection -> List Selection -> Prop where
  | objectLeaf
    {parentName responseName fieldName : Name}
    {arguments : List Argument}
    {directives : List DirectiveApplication}
    {currentSelectionSet childSelectionSet selectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    : objectTypeNameBool schema parentName = true
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> schema.lookupField parentName fieldName = some fieldDefinition
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> PathLocalSelectionSetObservableLeafAtRuntime schema parentName
          parentName currentSelectionSet selectionSet
  | objectChild
    {parentName childRuntimeType responseName fieldName : Name}
    {arguments : List Argument}
    {directives : List DirectiveApplication}
    {currentSelectionSet childSelectionSet selectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    : objectTypeNameBool schema parentName = true
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> schema.lookupField parentName fieldName = some fieldDefinition
      -> schema.isCompositeType fieldDefinition.outputType.namedType
      -> ((objectTypeNameBool schema fieldDefinition.outputType.namedType = true
            ∧ childRuntimeType = fieldDefinition.outputType.namedType)
          ∨ ((TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
                = true
              ∧ objectTypeNameBool schema fieldDefinition.outputType.namedType = false
              ∧ abstractRuntimeForFieldHeadDeep? schema parentName fieldName
                  arguments parentName currentSelectionSet
                = some childRuntimeType))
      -> PathLocalSelectionSetObservableLeafAtRuntime schema
          fieldDefinition.outputType.namedType childRuntimeType
          (fieldPairPathLocalNextSelectionSet schema parentName
            childRuntimeType fieldName arguments currentSelectionSet)
          childSelectionSet
      -> PathLocalSelectionSetObservableLeafAtRuntime schema parentName
          parentName currentSelectionSet selectionSet
  | abstractInlineFragment
    {parentName runtimeType : Name}
    {directives : List DirectiveApplication}
    {currentSelectionSet childSelectionSet selectionSet : List Selection}
    : objectTypeNameBool schema parentName = false
      -> objectTypeNameBool schema runtimeType = true
      -> schema.typeIncludesObjectBool parentName runtimeType = true
      -> Selection.inlineFragment (some runtimeType) directives childSelectionSet
          ∈ selectionSet
      -> PathLocalSelectionSetObservableLeafAtRuntime schema runtimeType
          runtimeType currentSelectionSet childSelectionSet
      -> PathLocalSelectionSetObservableLeafAtRuntime schema parentName
          runtimeType currentSelectionSet selectionSet

theorem selectionSet_nonempty_of_pathLocalSelectionSetObservableLeafAtRuntime
    {schema : Schema} {normalParentType runtimeType : Name}
    {currentSelectionSet selectionSet : List Selection}
    : PathLocalSelectionSetObservableLeafAtRuntime schema normalParentType
        runtimeType currentSelectionSet selectionSet
      -> selectionSet ≠ [] := by
  intro hobservable hempty
  cases hobservable with
  | objectLeaf _hobject hmem _hlookup _hleaf =>
      subst selectionSet
      simp at hmem
  | objectChild _hobject hmem _hlookup _hcomposite _hruntime _hchild =>
      subst selectionSet
      simp at hmem
  | abstractInlineFragment _hnonObject _hruntimeObject _hinclude hmem
      _hchild =>
      subst selectionSet
      simp at hmem

theorem pathLocalSelectionSetObservableLeafAtRuntime_runtime_object
    {schema : Schema} {normalParentType runtimeType : Name}
    {currentSelectionSet selectionSet : List Selection}
    : PathLocalSelectionSetObservableLeafAtRuntime schema normalParentType
        runtimeType currentSelectionSet selectionSet
      -> objectTypeNameBool schema runtimeType = true := by
  intro hobservable
  cases hobservable with
  | objectLeaf hobject _hmem _hlookup _hleaf =>
      exact hobject
  | objectChild hobject _hmem _hlookup _hcomposite _hruntime _hchild =>
      exact hobject
  | abstractInlineFragment _hnonObject hruntimeObject _hinclude _hmem
      _hchild =>
      exact hruntimeObject

theorem pathLocalSelectionSetObservableLeafAtRuntime_typeIncludes
    {schema : Schema} {normalParentType runtimeType : Name}
    {currentSelectionSet selectionSet : List Selection}
    : PathLocalSelectionSetObservableLeafAtRuntime schema normalParentType
        runtimeType currentSelectionSet selectionSet
      -> schema.typeIncludesObjectBool normalParentType runtimeType = true := by
  intro hobservable
  cases hobservable with
  | objectLeaf hobject _hmem _hlookup _hleaf =>
      exact typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject
  | objectChild hobject _hmem _hlookup _hcomposite _hruntime _hchild =>
      exact typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject
  | abstractInlineFragment _hnonObject _hruntimeObject hinclude _hmem
      _hchild =>
      exact hinclude

theorem pathLocalSelectionSetObservableLeafAtRuntime_runtime_eq_of_object
    {schema : Schema} {normalParentType runtimeType : Name}
    {currentSelectionSet selectionSet : List Selection}
    : objectTypeNameBool schema normalParentType = true
      -> PathLocalSelectionSetObservableLeafAtRuntime schema normalParentType
          runtimeType currentSelectionSet selectionSet
      -> runtimeType = normalParentType := by
  intro hobject hobservable
  cases hobservable with
  | objectLeaf =>
      rfl
  | objectChild =>
      rfl
  | abstractInlineFragment hnonObject _hruntimeObject _hinclude _hmem
      _hchild =>
      rw [hobject] at hnonObject
      simp at hnonObject

inductive PathLocalSelectionSetObservableLeafAtSelectedRuntime (schema : Schema)
    : Name -> Name -> List Selection -> List Selection -> Prop where
  | objectLeaf
    {parentName responseName fieldName : Name}
    {arguments : List Argument}
    {directives : List DirectiveApplication}
    {currentSelectionSet childSelectionSet selectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    : objectTypeNameBool schema parentName = true
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> schema.lookupField parentName fieldName = some fieldDefinition
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> PathLocalSelectionSetObservableLeafAtSelectedRuntime schema parentName
          parentName currentSelectionSet selectionSet
  | objectChild
    {parentName childRuntimeType responseName fieldName : Name}
    {arguments : List Argument}
    {directives : List DirectiveApplication}
    {currentSelectionSet childSelectionSet selectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    : objectTypeNameBool schema parentName = true
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> schema.lookupField parentName fieldName = some fieldDefinition
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> PathLocalSelectionSetObservableLeafAtSelectedRuntime schema
          fieldDefinition.outputType.namedType childRuntimeType
          (fieldPairPathLocalNextSelectionSet schema parentName
            childRuntimeType fieldName arguments currentSelectionSet)
          childSelectionSet
      -> PathLocalSelectionSetObservableLeafAtSelectedRuntime schema parentName
          parentName currentSelectionSet selectionSet
  | abstractInlineFragment
    {parentName runtimeType : Name}
    {directives : List DirectiveApplication}
    {currentSelectionSet childSelectionSet selectionSet : List Selection}
    : objectTypeNameBool schema parentName = false
      -> objectTypeNameBool schema runtimeType = true
      -> schema.typeIncludesObjectBool parentName runtimeType = true
      -> Selection.inlineFragment (some runtimeType) directives childSelectionSet
          ∈ selectionSet
      -> PathLocalSelectionSetObservableLeafAtSelectedRuntime schema runtimeType
          runtimeType currentSelectionSet childSelectionSet
      -> PathLocalSelectionSetObservableLeafAtSelectedRuntime schema parentName
          runtimeType currentSelectionSet selectionSet

theorem pathLocalSelectionSetObservableLeafAtSelectedRuntime_runtime_object
    {schema : Schema} {normalParentType runtimeType : Name}
    {currentSelectionSet selectionSet : List Selection}
    : PathLocalSelectionSetObservableLeafAtSelectedRuntime schema
        normalParentType runtimeType currentSelectionSet selectionSet
      -> objectTypeNameBool schema runtimeType = true := by
  intro hobservable
  cases hobservable with
  | objectLeaf hobject _hmem _hlookup _hleaf =>
      exact hobject
  | objectChild hobject _hmem _hlookup _hcomposite _hchild =>
      exact hobject
  | abstractInlineFragment _hnonObject hruntimeObject _hinclude _hmem
      _hchild =>
      exact hruntimeObject

theorem pathLocalSelectionSetObservableLeafAtSelectedRuntime_typeIncludes
    {schema : Schema} {normalParentType runtimeType : Name}
    {currentSelectionSet selectionSet : List Selection}
    : PathLocalSelectionSetObservableLeafAtSelectedRuntime schema
        normalParentType runtimeType currentSelectionSet selectionSet
      -> schema.typeIncludesObjectBool normalParentType runtimeType = true := by
  intro hobservable
  cases hobservable with
  | objectLeaf hobject _hmem _hlookup _hleaf =>
      exact typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject
  | objectChild hobject _hmem _hlookup _hcomposite _hchild =>
      exact typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject
  | abstractInlineFragment _hnonObject _hruntimeObject hinclude _hmem
      _hchild =>
      exact hinclude

theorem pathLocalSelectionSetObservableLeafAtSelectedRuntime_runtime_eq_of_object
    {schema : Schema} {normalParentType runtimeType : Name}
    {currentSelectionSet selectionSet : List Selection}
    : objectTypeNameBool schema normalParentType = true
      -> PathLocalSelectionSetObservableLeafAtSelectedRuntime schema
          normalParentType runtimeType currentSelectionSet selectionSet
      -> runtimeType = normalParentType := by
  intro hobject hobservable
  cases hobservable with
  | objectLeaf =>
      rfl
  | objectChild =>
      rfl
  | abstractInlineFragment hnonObject _hruntimeObject _hinclude _hmem
      _hchild =>
      rw [hobject] at hnonObject
      simp at hnonObject

inductive PathLocalSelectionSetObservableFieldSpineAtSelectedRuntime (schema : Schema)
    : Name -> Name -> List Selection -> List Selection
      -> List NormalSelectionSetObservableFieldStep -> Prop where
  | objectLeaf
    {parentName responseName fieldName : Name}
    {arguments : List Argument}
    {directives : List DirectiveApplication}
    {currentSelectionSet childSelectionSet selectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    : objectTypeNameBool schema parentName = true
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> schema.lookupField parentName fieldName = some fieldDefinition
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> PathLocalSelectionSetObservableFieldSpineAtSelectedRuntime schema
          parentName parentName currentSelectionSet selectionSet
          [{
            responseName := responseName,
            fieldName := fieldName,
            arguments := arguments,
            childRuntime := none
          }]
  | objectChild
    {parentName childRuntimeType responseName fieldName : Name}
    {arguments : List Argument}
    {directives : List DirectiveApplication}
    {currentSelectionSet childSelectionSet selectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    {childSpine : List NormalSelectionSetObservableFieldStep}
    : objectTypeNameBool schema parentName = true
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> schema.lookupField parentName fieldName = some fieldDefinition
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> PathLocalSelectionSetObservableFieldSpineAtSelectedRuntime schema
          fieldDefinition.outputType.namedType childRuntimeType
          (fieldPairPathLocalNextSelectionSet schema parentName
            childRuntimeType fieldName arguments currentSelectionSet)
          childSelectionSet childSpine
      -> PathLocalSelectionSetObservableFieldSpineAtSelectedRuntime schema
          parentName parentName currentSelectionSet selectionSet
          ({
              responseName := responseName,
              fieldName := fieldName,
              arguments := arguments,
              childRuntime := some childRuntimeType
            }
            :: childSpine)
  | abstractInlineFragment
    {parentName runtimeType : Name}
    {directives : List DirectiveApplication}
    {currentSelectionSet childSelectionSet selectionSet : List Selection}
    {childSpine : List NormalSelectionSetObservableFieldStep}
    : objectTypeNameBool schema parentName = false
      -> objectTypeNameBool schema runtimeType = true
      -> schema.typeIncludesObjectBool parentName runtimeType = true
      -> Selection.inlineFragment (some runtimeType) directives childSelectionSet
          ∈ selectionSet
      -> PathLocalSelectionSetObservableFieldSpineAtSelectedRuntime schema
          runtimeType runtimeType currentSelectionSet childSelectionSet
          childSpine
      -> PathLocalSelectionSetObservableFieldSpineAtSelectedRuntime schema
          parentName runtimeType currentSelectionSet selectionSet childSpine

theorem selectionSet_nonempty_of_pathLocalSelectionSetObservableFieldSpineAtSelectedRuntime
    {schema : Schema} {normalParentType runtimeType : Name}
    {currentSelectionSet selectionSet : List Selection}
    {fieldSpine : List NormalSelectionSetObservableFieldStep}
    : PathLocalSelectionSetObservableFieldSpineAtSelectedRuntime schema
        normalParentType runtimeType currentSelectionSet selectionSet
        fieldSpine
      -> selectionSet ≠ [] := by
  intro hobservable hempty
  cases hobservable with
  | objectLeaf _hobject hmem _hlookup _hleaf =>
      subst selectionSet
      simp at hmem
  | objectChild _hobject hmem _hlookup _hcomposite _hchild =>
      subst selectionSet
      simp at hmem
  | abstractInlineFragment _hnonObject _hruntimeObject _hinclude hmem
      _hchild =>
      subst selectionSet
      simp at hmem

theorem pathLocalSelectionSetObservableFieldSpineAtSelectedRuntime_runtime_object
    {schema : Schema} {normalParentType runtimeType : Name}
    {currentSelectionSet selectionSet : List Selection}
    {fieldSpine : List NormalSelectionSetObservableFieldStep}
    : PathLocalSelectionSetObservableFieldSpineAtSelectedRuntime schema
        normalParentType runtimeType currentSelectionSet selectionSet
        fieldSpine
      -> objectTypeNameBool schema runtimeType = true := by
  intro hobservable
  cases hobservable with
  | objectLeaf hobject _hmem _hlookup _hleaf =>
      exact hobject
  | objectChild hobject _hmem _hlookup _hcomposite _hchild =>
      exact hobject
  | abstractInlineFragment _hnonObject hruntimeObject _hinclude _hmem
      _hchild =>
      exact hruntimeObject

theorem pathLocalSelectionSetObservableFieldSpineAtSelectedRuntime_typeIncludes
    {schema : Schema} {normalParentType runtimeType : Name}
    {currentSelectionSet selectionSet : List Selection}
    {fieldSpine : List NormalSelectionSetObservableFieldStep}
    : PathLocalSelectionSetObservableFieldSpineAtSelectedRuntime schema
        normalParentType runtimeType currentSelectionSet selectionSet
        fieldSpine
      -> schema.typeIncludesObjectBool normalParentType runtimeType = true := by
  intro hobservable
  cases hobservable with
  | objectLeaf hobject _hmem _hlookup _hleaf =>
      exact typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject
  | objectChild hobject _hmem _hlookup _hcomposite _hchild =>
      exact typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject
  | abstractInlineFragment _hnonObject _hruntimeObject hinclude _hmem
      _hchild =>
      exact hinclude

theorem pathLocalSelectionSetObservableFieldSpineAtSelectedRuntime_runtime_eq_of_object
    {schema : Schema} {normalParentType runtimeType : Name}
    {currentSelectionSet selectionSet : List Selection}
    {fieldSpine : List NormalSelectionSetObservableFieldStep}
    : objectTypeNameBool schema normalParentType = true
      -> PathLocalSelectionSetObservableFieldSpineAtSelectedRuntime schema
          normalParentType runtimeType currentSelectionSet selectionSet
          fieldSpine
      -> runtimeType = normalParentType := by
  intro hobject hobservable
  cases hobservable with
  | objectLeaf =>
      rfl
  | objectChild =>
      rfl
  | abstractInlineFragment hnonObject _hruntimeObject _hinclude _hmem
      _hchild =>
      rw [hobject] at hnonObject
      simp at hnonObject

theorem pathLocalSelectionSetObservableFieldSpineAtSelectedRuntime_ne_nil
    {schema : Schema} {normalParentType runtimeType : Name}
    {currentSelectionSet selectionSet : List Selection}
    {fieldSpine : List NormalSelectionSetObservableFieldStep}
    : PathLocalSelectionSetObservableFieldSpineAtSelectedRuntime schema
        normalParentType runtimeType currentSelectionSet selectionSet
        fieldSpine
      -> fieldSpine ≠ [] := by
  intro hobservable
  induction hobservable with
  | objectLeaf =>
      simp
  | objectChild =>
      simp
  | abstractInlineFragment _hnonObject _hruntimeObject _hinclude _hmem
      _hchild ih =>
      exact ih

inductive SelectedFieldSpineRuntimeValid (schema : Schema)
    : Name -> Name -> List NormalSelectionSetObservableFieldStep -> Prop where
  | objectLeaf
    {parentType responseName fieldName : Name}
    {arguments : List Argument}
    {fieldDefinition : FieldDefinition}
    : objectTypeNameBool schema parentType = true
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> SelectedFieldSpineRuntimeValid schema parentType parentType
          [{
            responseName := responseName,
            fieldName := fieldName,
            arguments := arguments,
            childRuntime := none
          }]
  | objectChild
    {parentType childRuntimeType responseName fieldName : Name}
    {arguments : List Argument}
    {fieldDefinition : FieldDefinition}
    {childSpine : List NormalSelectionSetObservableFieldStep}
    : objectTypeNameBool schema parentType = true
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> SelectedFieldSpineRuntimeValid schema
          fieldDefinition.outputType.namedType childRuntimeType childSpine
      -> SelectedFieldSpineRuntimeValid schema parentType parentType
          ({
              responseName := responseName,
              fieldName := fieldName,
              arguments := arguments,
              childRuntime := some childRuntimeType
            }
            :: childSpine)
  | abstractRuntime
    {parentType runtimeType : Name}
    {spine : List NormalSelectionSetObservableFieldStep}
    : objectTypeNameBool schema parentType = false
      -> objectTypeNameBool schema runtimeType = true
      -> schema.typeIncludesObjectBool parentType runtimeType = true
      -> SelectedFieldSpineRuntimeValid schema runtimeType runtimeType spine
      -> SelectedFieldSpineRuntimeValid schema parentType runtimeType spine

theorem selectedFieldSpineRuntimeValid_runtime_object
    {schema : Schema} {normalParentType runtimeType : Name}
    {fieldSpine : List NormalSelectionSetObservableFieldStep}
    : SelectedFieldSpineRuntimeValid schema normalParentType runtimeType fieldSpine
      -> objectTypeNameBool schema runtimeType = true := by
  intro hvalid
  cases hvalid with
  | objectLeaf hobject _hlookup _hleaf =>
      exact hobject
  | objectChild hobject _hlookup _hcomposite _hchild =>
      exact hobject
  | abstractRuntime _hnonObject hruntimeObject _hinclude _hchild =>
      exact hruntimeObject

theorem selectedFieldSpineRuntimeValid_typeIncludes
    {schema : Schema} {normalParentType runtimeType : Name}
    {fieldSpine : List NormalSelectionSetObservableFieldStep}
    : SelectedFieldSpineRuntimeValid schema normalParentType runtimeType fieldSpine
      -> schema.typeIncludesObjectBool normalParentType runtimeType = true := by
  intro hvalid
  cases hvalid with
  | objectLeaf hobject _hlookup _hleaf =>
      exact typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject
  | objectChild hobject _hlookup _hcomposite _hchild =>
      exact typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject
  | abstractRuntime _hnonObject _hruntimeObject hinclude _hchild =>
      exact hinclude

theorem selectedFieldSpineRuntimeValid_of_observableFieldSpineAtSelectedRuntime
    {schema : Schema} {normalParentType runtimeType : Name}
    {currentSelectionSet selectionSet : List Selection}
    {fieldSpine : List NormalSelectionSetObservableFieldStep}
    : PathLocalSelectionSetObservableFieldSpineAtSelectedRuntime schema
        normalParentType runtimeType currentSelectionSet selectionSet
        fieldSpine
      -> SelectedFieldSpineRuntimeValid schema normalParentType runtimeType
          fieldSpine := by
  intro hobservable
  induction hobservable with
  | objectLeaf hobject _hmem hlookup hleaf =>
      exact
        SelectedFieldSpineRuntimeValid.objectLeaf hobject hlookup hleaf
  | objectChild hobject _hmem hlookup hcomposite _hchild ih =>
      exact
        SelectedFieldSpineRuntimeValid.objectChild hobject hlookup
          hcomposite ih
  | abstractInlineFragment hnonObject hruntimeObject hinclude _hmem
      _hchild ih =>
      exact
        SelectedFieldSpineRuntimeValid.abstractRuntime hnonObject
          hruntimeObject hinclude ih

theorem pathLocalSelectionSetObservableLeafAtSelectedRuntime_of_observableResponsePath_valid_normal
    {schema : Schema} {variableDefinitions : List VariableDefinition} {parentType : Name}
    {selectionSet : List Selection} {responsePath : List Name}
    : NormalSelectionSetObservableResponsePath schema parentType selectionSet responsePath
      -> Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> ∃ runtimeType,
          schema.typeIncludesObjectBool parentType runtimeType = true
          ∧ ∀ currentSelectionSet,
              PathLocalSelectionSetObservableLeafAtSelectedRuntime schema
                parentType runtimeType currentSelectionSet selectionSet := by
  intro hpath
  induction hpath with
  | objectLeaf hobject hmem hlookup hleaf =>
      rename_i pathParentType responseName fieldName arguments directives
        childSelectionSet pathSelectionSet fieldDefinition
      intro _hvalid _hnormal
      exact
        ⟨pathParentType,
          typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject,
          fun currentSelectionSet =>
            PathLocalSelectionSetObservableLeafAtSelectedRuntime.objectLeaf
              hobject hmem hlookup hleaf⟩
  | objectChild hobject hmem hlookup hcomposite hchildPath ih =>
      rename_i pathParentType responseName fieldName arguments directives
        childSelectionSet pathSelectionSet fieldDefinition childPath
      intro hvalid hnormal
      have hchildNonempty : childSelectionSet ≠ [] :=
        normalSelectionSetResponsePath_selectionSet_nonempty
          (NormalSelectionSetObservableResponsePath.to_responsePath
            hchildPath)
      rcases
          selectionSetValid_field_lookup_leaf_or_composite_child hvalid
            hmem with
        ⟨candidateDefinition, hcandidateLookup, hkind⟩
      have hcandidateEq : candidateDefinition = fieldDefinition := by
        rw [hlookup] at hcandidateLookup
        exact Option.some.inj hcandidateLookup.symm
      subst candidateDefinition
      have hchildNormal :
          selectionSetNormal schema fieldDefinition.outputType.namedType
            childSelectionSet :=
        selectionSetNormal_field_child_of_mem_lookup hnormal hmem hlookup
      rcases hkind with hleaf | hchildValidAndComposite
      · exact False.elim (hchildNonempty hleaf.2)
      · rcases
            ih hchildValidAndComposite.2.2 hchildNormal with
          ⟨childRuntime, _hchildInclude, hchildObservable⟩
        exact
          ⟨pathParentType,
            typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject,
            fun currentSelectionSet =>
              PathLocalSelectionSetObservableLeafAtSelectedRuntime.objectChild
                hobject hmem hlookup hcomposite
                (hchildObservable
                  (fieldPairPathLocalNextSelectionSet schema pathParentType
                    childRuntime fieldName arguments
                    currentSelectionSet))⟩
  | abstractInlineFragment hnonObject hmem hchildPath ih =>
      rename_i pathParentType typeCondition directives childSelectionSet
        pathSelectionSet childPath
      intro hvalid hnormal
      have hchildValid :
          Validation.selectionSetValid schema variableDefinitions
            typeCondition childSelectionSet :=
        selectionSetValid_inlineFragment_some_child_of_mem hvalid hmem
      rcases selectionSetNormal_inlineFragment_child_of_mem hnormal hmem with
        ⟨htypeObject, hchildNormal⟩
      have hoverlap : schema.typesOverlap pathParentType typeCondition :=
        selectionSetValid_inlineFragment_some_typesOverlap_of_mem hvalid
          hmem
      have hinclude :
          schema.typeIncludesObjectBool pathParentType typeCondition =
            true :=
        typeIncludesObjectBool_of_typesOverlap_object schema hoverlap
          htypeObject
      have htypeObjectBool :
          objectTypeNameBool schema typeCondition = true :=
        objectTypeNameBool_eq_true_of_objectType_forNormality schema
          htypeObject
      rcases ih hchildValid hchildNormal with
        ⟨childRuntime, _hchildInclude, hchildObservable⟩
      have hruntimeEq : childRuntime = typeCondition :=
        pathLocalSelectionSetObservableLeafAtSelectedRuntime_runtime_eq_of_object
          htypeObjectBool (hchildObservable [])
      subst childRuntime
      exact
        ⟨typeCondition, hinclude,
          fun currentSelectionSet =>
            PathLocalSelectionSetObservableLeafAtSelectedRuntime.abstractInlineFragment
              hnonObject htypeObjectBool hinclude hmem
              (hchildObservable currentSelectionSet)⟩

theorem pathLocalSelectionSetObservableFieldSpineAtSelectedRuntime_of_observableResponsePath_valid_normal
    {schema : Schema} {variableDefinitions : List VariableDefinition} {parentType : Name}
    {selectionSet : List Selection} {responsePath : List Name}
    : NormalSelectionSetObservableResponsePath schema parentType selectionSet responsePath
      -> Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> ∃ runtimeType fieldSpine,
          schema.typeIncludesObjectBool parentType runtimeType = true
          ∧ ∀ currentSelectionSet,
              PathLocalSelectionSetObservableFieldSpineAtSelectedRuntime schema
                parentType runtimeType currentSelectionSet selectionSet
                fieldSpine := by
  intro hpath
  induction hpath with
  | objectLeaf hobject hmem hlookup hleaf =>
      rename_i pathParentType responseName fieldName arguments directives
        childSelectionSet pathSelectionSet fieldDefinition
      intro _hvalid _hnormal
      exact
        ⟨pathParentType,
          [{ responseName := responseName, fieldName := fieldName,
             arguments := arguments, childRuntime := none }],
          typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject,
          fun currentSelectionSet =>
            PathLocalSelectionSetObservableFieldSpineAtSelectedRuntime.objectLeaf
              hobject hmem hlookup hleaf⟩
  | objectChild hobject hmem hlookup hcomposite hchildPath ih =>
      rename_i pathParentType responseName fieldName arguments directives
        childSelectionSet pathSelectionSet fieldDefinition childPath
      intro hvalid hnormal
      have hchildNonempty : childSelectionSet ≠ [] :=
        normalSelectionSetResponsePath_selectionSet_nonempty
          (NormalSelectionSetObservableResponsePath.to_responsePath
            hchildPath)
      rcases
          selectionSetValid_field_lookup_leaf_or_composite_child hvalid
            hmem with
        ⟨candidateDefinition, hcandidateLookup, hkind⟩
      have hcandidateEq : candidateDefinition = fieldDefinition := by
        rw [hlookup] at hcandidateLookup
        exact Option.some.inj hcandidateLookup.symm
      subst candidateDefinition
      have hchildNormal :
          selectionSetNormal schema fieldDefinition.outputType.namedType
            childSelectionSet :=
        selectionSetNormal_field_child_of_mem_lookup hnormal hmem hlookup
      rcases hkind with hleaf | hchildValidAndComposite
      · exact False.elim (hchildNonempty hleaf.2)
      · rcases
            ih hchildValidAndComposite.2.2 hchildNormal with
          ⟨childRuntime, childSpine, _hchildInclude,
            hchildObservable⟩
        exact
          ⟨pathParentType,
            { responseName := responseName, fieldName := fieldName,
              arguments := arguments, childRuntime := some childRuntime } ::
              childSpine,
            typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject,
            fun currentSelectionSet =>
              PathLocalSelectionSetObservableFieldSpineAtSelectedRuntime.objectChild
                hobject hmem hlookup hcomposite
                (hchildObservable
                  (fieldPairPathLocalNextSelectionSet schema pathParentType
                    childRuntime fieldName arguments
                    currentSelectionSet))⟩
  | abstractInlineFragment hnonObject hmem hchildPath ih =>
      rename_i pathParentType typeCondition directives childSelectionSet
        pathSelectionSet childPath
      intro hvalid hnormal
      have hchildValid :
          Validation.selectionSetValid schema variableDefinitions
            typeCondition childSelectionSet :=
        selectionSetValid_inlineFragment_some_child_of_mem hvalid hmem
      rcases selectionSetNormal_inlineFragment_child_of_mem hnormal hmem with
        ⟨htypeObject, hchildNormal⟩
      have hoverlap : schema.typesOverlap pathParentType typeCondition :=
        selectionSetValid_inlineFragment_some_typesOverlap_of_mem hvalid
          hmem
      have hinclude :
          schema.typeIncludesObjectBool pathParentType typeCondition =
            true :=
        typeIncludesObjectBool_of_typesOverlap_object schema hoverlap
          htypeObject
      have htypeObjectBool :
          objectTypeNameBool schema typeCondition = true :=
        objectTypeNameBool_eq_true_of_objectType_forNormality schema
          htypeObject
      rcases ih hchildValid hchildNormal with
        ⟨childRuntime, childSpine, _hchildInclude, hchildObservable⟩
      have hruntimeEq : childRuntime = typeCondition :=
        pathLocalSelectionSetObservableFieldSpineAtSelectedRuntime_runtime_eq_of_object
          htypeObjectBool (hchildObservable [])
      subst childRuntime
      exact
        ⟨typeCondition, childSpine, hinclude,
          fun currentSelectionSet =>
            PathLocalSelectionSetObservableFieldSpineAtSelectedRuntime.abstractInlineFragment
              hnonObject htypeObjectBool hinclude hmem
              (hchildObservable currentSelectionSet)⟩

inductive FieldPairSelectedPathProbeRef where
  | root
  | target
    (tag : FieldPairProbeTag)
    (currentSelectionSet : List Selection)
    (spine : List NormalSelectionSetObservableFieldStep)
  | filler

noncomputable def selectedObservableFieldSpineNext?
    (fieldName : Name) (arguments : List Argument)
    : List NormalSelectionSetObservableFieldStep
      -> Option (Option Name × List NormalSelectionSetObservableFieldStep)
  | [] => none
  | step :: rest => by
      classical
      exact
        if step.fieldName = fieldName
            ∧ Argument.argumentsEquivalent arguments step.arguments then
          some (step.childRuntime, rest)
        else
          none

theorem selectedObservableFieldSpineNext?_eq_of_argumentsEquivalent
    (fieldName : Name) {firstArguments laterArguments : List Argument}
    (hequivalent : Argument.argumentsEquivalent firstArguments laterArguments)
    : ∀ spine,
        selectedObservableFieldSpineNext? fieldName firstArguments spine
        = selectedObservableFieldSpineNext? fieldName laterArguments spine
  | [] => by
      simp [selectedObservableFieldSpineNext?]
  | step :: rest => by
      have hargumentsIff :
          Argument.argumentsEquivalent firstArguments step.arguments
            ↔ Argument.argumentsEquivalent laterArguments step.arguments := by
        constructor
        · intro hfirst
          exact argumentsEquivalent_trans
            (FieldMerge.argumentsEquivalent_symm hequivalent) hfirst
        · intro hlater
          exact argumentsEquivalent_trans hequivalent hlater
      have hmatchIff :
          (step.fieldName = fieldName
              ∧ Argument.argumentsEquivalent firstArguments
                step.arguments)
            ↔
            (step.fieldName = fieldName
              ∧ Argument.argumentsEquivalent laterArguments
                step.arguments) := by
        constructor
        · intro h
          exact ⟨h.1, hargumentsIff.mp h.2⟩
        · intro h
          exact ⟨h.1, hargumentsIff.mpr h.2⟩
      by_cases hfirst :
          step.fieldName = fieldName
            ∧ Argument.argumentsEquivalent firstArguments step.arguments
      · have hlater :
            step.fieldName = fieldName
              ∧ Argument.argumentsEquivalent laterArguments step.arguments :=
          hmatchIff.mp hfirst
        simp [selectedObservableFieldSpineNext?, hfirst, hlater]
      · have hlater :
            ¬ (step.fieldName = fieldName
              ∧ Argument.argumentsEquivalent laterArguments step.arguments) := by
          intro hlater
          exact hfirst (hmatchIff.mpr hlater)
        simp [selectedObservableFieldSpineNext?, hfirst, hlater]

noncomputable def selectedObservableFieldSpineTailForRuntime
    (runtimeType fieldName : Name) (arguments : List Argument)
    (spine : List NormalSelectionSetObservableFieldStep)
    : List NormalSelectionSetObservableFieldStep :=
  match selectedObservableFieldSpineNext? fieldName arguments spine with
  | some (some selectedRuntime, rest) =>
      if selectedRuntime = runtimeType then rest else []
  | _ => []

noncomputable def fieldPairSelectedPathProbeHeadResolverValue
    (schema : Schema) (currentSelectionSet : List Selection)
    (parentType fieldName : Name) (arguments : List Argument)
    (tag : FieldPairProbeTag)
    (spine : List NormalSelectionSetObservableFieldStep)
    : TypeRef -> Execution.ResolverValue FieldPairSelectedPathProbeRef
  | .named typeName =>
      if (TypeRef.named typeName).isCompositeBool schema then
        if objectTypeNameBool schema typeName then
          .object typeName
            (FieldPairSelectedPathProbeRef.target tag
              (fieldPairPathLocalNextSelectionSet schema parentType
                typeName fieldName arguments currentSelectionSet)
              (selectedObservableFieldSpineTailForRuntime typeName
                fieldName arguments spine))
        else
          match selectedObservableFieldSpineNext? fieldName arguments spine with
          | some (some runtimeType, rest) =>
              .object runtimeType
                (FieldPairSelectedPathProbeRef.target tag
                  (fieldPairPathLocalNextSelectionSet schema parentType
                    runtimeType fieldName arguments currentSelectionSet)
                  rest)
          | _ =>
              match abstractRuntimeForFieldHeadDeep? schema parentType fieldName
                      arguments parentType currentSelectionSet with
              | some runtimeType =>
                  .object runtimeType
                    (FieldPairSelectedPathProbeRef.target tag
                      (fieldPairPathLocalNextSelectionSet schema parentType
                        runtimeType fieldName arguments currentSelectionSet)
                      [])
              | none =>
                  .object typeName (FieldPairSelectedPathProbeRef.target tag [] [])
      else
        .scalar tag.scalar
  | .list inner =>
      .list
        [fieldPairSelectedPathProbeHeadResolverValue schema
          currentSelectionSet parentType fieldName arguments tag spine inner]
  | .nonNull inner =>
      fieldPairSelectedPathProbeHeadResolverValue schema currentSelectionSet
        parentType fieldName arguments tag spine inner

theorem selectedObservableFieldSpineTailForRuntime_eq_of_argumentsEquivalent
    (runtimeType fieldName : Name)
    {firstArguments laterArguments : List Argument}
    (hequivalent : Argument.argumentsEquivalent firstArguments laterArguments)
    (spine : List NormalSelectionSetObservableFieldStep)
    : selectedObservableFieldSpineTailForRuntime runtimeType fieldName
        firstArguments spine
      = selectedObservableFieldSpineTailForRuntime runtimeType fieldName
          laterArguments spine := by
  have hnext :=
    selectedObservableFieldSpineNext?_eq_of_argumentsEquivalent fieldName
      hequivalent spine
  simp [selectedObservableFieldSpineTailForRuntime, hnext]

theorem fieldPairSelectedPathProbeHeadResolverValue_eq_of_argumentsEquivalent
    (schema : Schema) (currentSelectionSet : List Selection)
    (parentType fieldName : Name)
    {firstArguments laterArguments : List Argument}
    (tag : FieldPairProbeTag)
    (spine : List NormalSelectionSetObservableFieldStep)
    : Argument.argumentsEquivalent firstArguments laterArguments
      -> ∀ outputType,
          fieldPairSelectedPathProbeHeadResolverValue schema currentSelectionSet
            parentType fieldName firstArguments tag spine outputType
          = fieldPairSelectedPathProbeHeadResolverValue schema currentSelectionSet
              parentType fieldName laterArguments tag spine outputType
  | hequivalent, .named typeName => by
      have hselected :=
        selectedObservableFieldSpineNext?_eq_of_argumentsEquivalent fieldName
          hequivalent spine
      have htail :
          selectedObservableFieldSpineTailForRuntime typeName fieldName
              firstArguments spine =
            selectedObservableFieldSpineTailForRuntime typeName fieldName
              laterArguments spine :=
        selectedObservableFieldSpineTailForRuntime_eq_of_argumentsEquivalent
          typeName fieldName hequivalent spine
      have hruntime :=
        abstractRuntimeForFieldHeadDeep?_eq_of_argumentsEquivalent schema
          parentType fieldName hequivalent parentType currentSelectionSet
      have hnext :
          ∀ runtimeType,
            fieldPairPathLocalNextSelectionSet schema parentType runtimeType
              fieldName firstArguments currentSelectionSet =
            fieldPairPathLocalNextSelectionSet schema parentType runtimeType
              fieldName laterArguments currentSelectionSet := by
        intro runtimeType
        exact
          fieldPairPathLocalNextSelectionSet_eq_of_argumentsEquivalent
            schema parentType runtimeType fieldName hequivalent
            currentSelectionSet
      by_cases hcomposite :
          (TypeRef.named typeName).isCompositeBool schema
      · by_cases hobject : objectTypeNameBool schema typeName
        · simp [fieldPairSelectedPathProbeHeadResolverValue, hcomposite,
            hobject, hnext, htail]
        · simp [fieldPairSelectedPathProbeHeadResolverValue, hcomposite,
            hobject, hselected, hruntime, hnext]
      · simp [fieldPairSelectedPathProbeHeadResolverValue, hcomposite]
  | hequivalent, .list inner => by
      have hinner :=
        fieldPairSelectedPathProbeHeadResolverValue_eq_of_argumentsEquivalent
          schema currentSelectionSet parentType fieldName tag spine
          hequivalent inner
      simp [fieldPairSelectedPathProbeHeadResolverValue, hinner]
  | hequivalent, .nonNull inner => by
      exact
        fieldPairSelectedPathProbeHeadResolverValue_eq_of_argumentsEquivalent
          schema currentSelectionSet parentType fieldName tag spine
          hequivalent inner

theorem fieldPairSelectedPathProbeHeadResolverValue_selected_eq_objectProbeResolverValueWithRuntime
    (schema : Schema) (currentSelectionSet : List Selection)
    (parentType fieldName runtimeType : Name) (arguments : List Argument)
    (tag : FieldPairProbeTag) (spine tail : List NormalSelectionSetObservableFieldStep)
    : ∀ outputType,
        selectedObservableFieldSpineNext? fieldName arguments spine
          = some (some runtimeType, tail)
        -> ((objectTypeNameBool schema outputType.namedType = true
              ∧ runtimeType = outputType.namedType)
            ∨ ((TypeRef.named outputType.namedType).isCompositeBool schema = true
                ∧ objectTypeNameBool schema outputType.namedType = false))
        -> fieldPairSelectedPathProbeHeadResolverValue schema currentSelectionSet
              parentType fieldName arguments tag spine outputType
            = objectProbeResolverValueWithRuntime runtimeType
                (FieldPairSelectedPathProbeRef.target tag
                  (fieldPairPathLocalNextSelectionSet schema parentType
                    runtimeType fieldName arguments currentSelectionSet)
                  tail)
                outputType
  | .named typeName, hselected, hcase => by
      rcases hcase with hobject | habstract
      · rcases hobject with ⟨hobject, hruntime⟩
        subst runtimeType
        have hobjectNamed :
            objectTypeNameBool schema typeName = true := by
          simpa [TypeRef.namedType] using hobject
        have hselectedNamed :
            selectedObservableFieldSpineNext? fieldName arguments spine =
              some (some typeName, tail) := by
          simpa [TypeRef.namedType] using hselected
        have htail :
            selectedObservableFieldSpineTailForRuntime typeName fieldName
                arguments spine =
              tail := by
          simp [selectedObservableFieldSpineTailForRuntime, hselectedNamed]
        have hcomposite :
            (TypeRef.named typeName).isCompositeBool schema = true := by
          unfold objectTypeNameBool at hobjectNamed
          unfold TypeRef.isCompositeBool TypeRef.namedType
          cases hlookup : schema.lookupType typeName with
          | none =>
              simp [hlookup] at hobjectNamed
          | some typeDefinition =>
              cases typeDefinition <;> simp [hlookup] at hobjectNamed ⊢
        simp [fieldPairSelectedPathProbeHeadResolverValue,
          objectProbeResolverValueWithRuntime, TypeRef.namedType,
          hcomposite, hobjectNamed, htail]
      · rcases habstract with ⟨hcomposite, hnonObject⟩
        have hcompositeNamed :
            (TypeRef.named typeName).isCompositeBool schema = true := by
          simpa [TypeRef.namedType] using hcomposite
        have hnonObjectNamed :
            objectTypeNameBool schema typeName = false := by
          simpa [TypeRef.namedType] using hnonObject
        simp [fieldPairSelectedPathProbeHeadResolverValue,
          objectProbeResolverValueWithRuntime, hcompositeNamed,
          hnonObjectNamed, hselected]
  | .list inner, hselected, hcase => by
      have hinner :=
        fieldPairSelectedPathProbeHeadResolverValue_selected_eq_objectProbeResolverValueWithRuntime
          schema currentSelectionSet parentType fieldName runtimeType
          arguments tag spine tail inner hselected
          (by simpa [TypeRef.namedType] using hcase)
      simpa [fieldPairSelectedPathProbeHeadResolverValue,
        objectProbeResolverValueWithRuntime, TypeRef.namedType] using hinner
  | .nonNull inner, hselected, hcase => by
      exact
        fieldPairSelectedPathProbeHeadResolverValue_selected_eq_objectProbeResolverValueWithRuntime
          schema currentSelectionSet parentType fieldName runtimeType
          arguments tag spine tail inner hselected
          (by simpa [TypeRef.namedType] using hcase)

theorem fieldPairSelectedPathProbeHeadResolverValue_object_eq_objectProbeResolverValueWithRuntime
    (schema : Schema) (currentSelectionSet : List Selection) (parentType fieldName : Name)
    (arguments : List Argument) (tag : FieldPairProbeTag)
    (spine : List NormalSelectionSetObservableFieldStep)
    : ∀ outputType,
        objectTypeNameBool schema outputType.namedType = true
        -> fieldPairSelectedPathProbeHeadResolverValue schema
              currentSelectionSet parentType fieldName arguments tag spine
              outputType
            = objectProbeResolverValueWithRuntime outputType.namedType
                (FieldPairSelectedPathProbeRef.target tag
                  (fieldPairPathLocalNextSelectionSet schema parentType
                    outputType.namedType fieldName arguments currentSelectionSet)
                  (selectedObservableFieldSpineTailForRuntime
                    outputType.namedType fieldName arguments spine))
                outputType
  | .named typeName, hobject => by
      have hobjectNamed :
          objectTypeNameBool schema typeName = true := by
        simpa [TypeRef.namedType] using hobject
      have hcomposite :
          (TypeRef.named typeName).isCompositeBool schema = true := by
        unfold objectTypeNameBool at hobjectNamed
        unfold TypeRef.isCompositeBool TypeRef.namedType
        cases hlookup : schema.lookupType typeName with
        | none =>
            simp [hlookup] at hobjectNamed
        | some typeDefinition =>
            cases typeDefinition <;> simp [hlookup] at hobjectNamed ⊢
      simp [fieldPairSelectedPathProbeHeadResolverValue,
        objectProbeResolverValueWithRuntime, TypeRef.namedType, hcomposite,
        hobjectNamed]
  | .list inner, hobject => by
      have hinner :=
        fieldPairSelectedPathProbeHeadResolverValue_object_eq_objectProbeResolverValueWithRuntime
          schema currentSelectionSet parentType fieldName arguments tag
          spine inner (by simpa [TypeRef.namedType] using hobject)
      simpa [fieldPairSelectedPathProbeHeadResolverValue,
        objectProbeResolverValueWithRuntime, TypeRef.namedType] using hinner
  | .nonNull inner, hobject => by
      exact
        fieldPairSelectedPathProbeHeadResolverValue_object_eq_objectProbeResolverValueWithRuntime
          schema currentSelectionSet parentType fieldName arguments tag
          spine inner (by simpa [TypeRef.namedType] using hobject)

theorem fieldPairSelectedPathProbeHeadResolverValue_abstractFallback_eq_objectProbeResolverValueWithRuntime
    (schema : Schema) (currentSelectionSet : List Selection)
    (parentType fieldName runtimeType : Name) (arguments : List Argument)
    (tag : FieldPairProbeTag) (spine : List NormalSelectionSetObservableFieldStep)
    : ∀ outputType,
        (TypeRef.named outputType.namedType).isCompositeBool schema = true
        -> objectTypeNameBool schema outputType.namedType = false
        -> selectedObservableFieldSpineNext? fieldName arguments spine = none
        -> abstractRuntimeForFieldHeadDeep? schema parentType fieldName
              arguments parentType currentSelectionSet
            = some runtimeType
        -> fieldPairSelectedPathProbeHeadResolverValue schema currentSelectionSet
              parentType fieldName arguments tag spine outputType
            = objectProbeResolverValueWithRuntime runtimeType
                (FieldPairSelectedPathProbeRef.target tag
                  (fieldPairPathLocalNextSelectionSet schema parentType
                    runtimeType fieldName arguments currentSelectionSet)
                  [])
                outputType
  | .named typeName, hcomposite, hnonObject, hselectedNone, hruntime => by
      have hcompositeNamed :
          (TypeRef.named typeName).isCompositeBool schema = true := by
        simpa [TypeRef.namedType] using hcomposite
      have hnonObjectNamed :
          objectTypeNameBool schema typeName = false := by
        simpa [TypeRef.namedType] using hnonObject
      simp [fieldPairSelectedPathProbeHeadResolverValue,
        objectProbeResolverValueWithRuntime, hcompositeNamed,
        hnonObjectNamed, hselectedNone, hruntime]
  | .list inner, hcomposite, hnonObject, hselectedNone, hruntime => by
      have hinner :=
        fieldPairSelectedPathProbeHeadResolverValue_abstractFallback_eq_objectProbeResolverValueWithRuntime
          schema currentSelectionSet parentType fieldName runtimeType
          arguments tag spine inner
          (by simpa [TypeRef.namedType] using hcomposite)
          (by simpa [TypeRef.namedType] using hnonObject)
          hselectedNone hruntime
      simpa [fieldPairSelectedPathProbeHeadResolverValue,
        objectProbeResolverValueWithRuntime, TypeRef.namedType] using hinner
  | .nonNull inner, hcomposite, hnonObject, hselectedNone, hruntime => by
      exact
        fieldPairSelectedPathProbeHeadResolverValue_abstractFallback_eq_objectProbeResolverValueWithRuntime
          schema currentSelectionSet parentType fieldName runtimeType
          arguments tag spine inner
          (by simpa [TypeRef.namedType] using hcomposite)
          (by simpa [TypeRef.namedType] using hnonObject)
          hselectedNone hruntime

noncomputable def fieldPairSelectedPathProbeResolve
    (schema : Schema)
    (leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (targetParent leftField rightField : Name)
    (leftArguments rightArguments : List Argument)
    (leftRuntime rightRuntime parentType fieldName : Name)
    (arguments : List Argument)
    (source : Execution.ResolverValue FieldPairSelectedPathProbeRef)
    : Option (Execution.ResolverValue FieldPairSelectedPathProbeRef) := by
  classical
  exact
    match source with
    | .object _ (FieldPairSelectedPathProbeRef.target tag currentSelectionSet
        spine) =>
        match schema.lookupField parentType fieldName with
        | none => none
        | some fieldDefinition =>
            some
              (fieldPairSelectedPathProbeHeadResolverValue schema
                currentSelectionSet parentType fieldName arguments tag spine
                fieldDefinition.outputType)
    | .object _ FieldPairSelectedPathProbeRef.root =>
        match schema.lookupField parentType fieldName with
        | none => none
        | some fieldDefinition =>
            if fieldProbeTarget targetParent leftField leftArguments
                parentType fieldName arguments then
              some
                (objectProbeResolverValueWithRuntime leftRuntime
                  (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                    leftInitialSelectionSet leftInitialSpine)
                  fieldDefinition.outputType)
            else if fieldProbeTarget targetParent rightField rightArguments
                parentType fieldName arguments then
              some
                (objectProbeResolverValueWithRuntime rightRuntime
                  (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                    rightInitialSelectionSet rightInitialSpine)
                  fieldDefinition.outputType)
            else
              none
    | .object _ FieldPairSelectedPathProbeRef.filler => none
    | _ => none

noncomputable def fieldPairSelectedPathProbeResolvers
    (schema : Schema)
    (leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (targetParent leftField rightField : Name)
    (leftArguments rightArguments : List Argument)
    (leftRuntime rightRuntime : Name)
    : Execution.Resolvers FieldPairSelectedPathProbeRef where
  resolve parentType fieldName arguments source :=
    fieldPairSelectedPathProbeResolve schema leftInitialSelectionSet
      rightInitialSelectionSet leftInitialSpine rightInitialSpine
      targetParent leftField rightField leftArguments rightArguments
      leftRuntime rightRuntime parentType fieldName arguments source
  resolve_argumentsEquivalent := by
    intro parentType fieldName firstArguments laterArguments source
      harguments
    classical
    cases hlookup : schema.lookupField parentType fieldName with
    | none =>
        cases source <;>
          simp [fieldPairSelectedPathProbeResolve, hlookup]
    | some fieldDefinition =>
        cases source with
        | null =>
            simp [fieldPairSelectedPathProbeResolve]
        | scalar value =>
            simp [fieldPairSelectedPathProbeResolve]
        | list values =>
            simp [fieldPairSelectedPathProbeResolve]
        | object runtimeType ref =>
            cases ref with
            | root =>
                have hleftIff :=
                  fieldProbeTarget_iff_of_argumentsEquivalent targetParent
                    leftField leftArguments parentType fieldName
                    firstArguments laterArguments harguments
                have hrightIff :=
                  fieldProbeTarget_iff_of_argumentsEquivalent targetParent
                    rightField rightArguments parentType fieldName
                    firstArguments laterArguments harguments
                by_cases hfirstLeft :
                    fieldProbeTarget targetParent leftField leftArguments
                      parentType fieldName firstArguments
                · have hlaterLeft :
                      fieldProbeTarget targetParent leftField leftArguments
                        parentType fieldName laterArguments :=
                    hleftIff.mp hfirstLeft
                  simp [fieldPairSelectedPathProbeResolve, hlookup,
                    hfirstLeft, hlaterLeft]
                · have hlaterLeft :
                      ¬ fieldProbeTarget targetParent leftField leftArguments
                        parentType fieldName laterArguments := by
                    intro hlater
                    exact hfirstLeft (hleftIff.mpr hlater)
                  by_cases hfirstRight :
                      fieldProbeTarget targetParent rightField rightArguments
                        parentType fieldName firstArguments
                  · have hlaterRight :
                        fieldProbeTarget targetParent rightField
                          rightArguments parentType fieldName
                          laterArguments :=
                      hrightIff.mp hfirstRight
                    simp [fieldPairSelectedPathProbeResolve, hlookup,
                      hfirstLeft, hlaterLeft, hfirstRight, hlaterRight]
                  · have hlaterRight :
                        ¬ fieldProbeTarget targetParent rightField
                          rightArguments parentType fieldName
                          laterArguments := by
                      intro hlater
                      exact hfirstRight (hrightIff.mpr hlater)
                    simp [fieldPairSelectedPathProbeResolve, hlookup,
                      hfirstLeft, hlaterLeft, hfirstRight, hlaterRight]
            | target tag currentSelectionSet spine =>
                have hvalue :=
                  fieldPairSelectedPathProbeHeadResolverValue_eq_of_argumentsEquivalent
                    schema currentSelectionSet parentType fieldName tag
                    spine harguments fieldDefinition.outputType
                simp [fieldPairSelectedPathProbeResolve, hlookup, hvalue]
            | filler =>
                simp [fieldPairSelectedPathProbeResolve]

theorem selectedObservableFieldSpineNext?_cons_self
    (step : NormalSelectionSetObservableFieldStep)
    (rest : List NormalSelectionSetObservableFieldStep)
    : selectedObservableFieldSpineNext? step.fieldName step.arguments (step :: rest)
      = some (step.childRuntime, rest) := by
  simp [selectedObservableFieldSpineNext?,
    argumentsEquivalent_refl_forSyntaxDiff]

theorem selectedObservableFieldSpineTailForRuntime_cons_self
    (step : NormalSelectionSetObservableFieldStep)
    (rest : List NormalSelectionSetObservableFieldStep)
    {runtimeType : Name}
    : step.childRuntime = some runtimeType
      -> selectedObservableFieldSpineTailForRuntime runtimeType step.fieldName
            step.arguments (step :: rest)
          = rest := by
  intro hchildRuntime
  have hnext :=
    selectedObservableFieldSpineNext?_cons_self step rest
  simp [selectedObservableFieldSpineTailForRuntime, hnext,
    hchildRuntime]

theorem selectedFieldSpineRuntimeValid_child_of_selectedNext
    {schema : Schema} {parentType runtimeType fieldName : Name}
    {arguments : List Argument}
    {spine tail : List NormalSelectionSetObservableFieldStep}
    {fieldDefinition : FieldDefinition} {selectedRuntime : Name}
    : SelectedFieldSpineRuntimeValid schema parentType runtimeType spine
      -> objectTypeNameBool schema parentType = true
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> selectedObservableFieldSpineNext? fieldName arguments spine
          = some (some selectedRuntime, tail)
      -> (((objectTypeNameBool schema fieldDefinition.outputType.namedType = true
              ∧ selectedRuntime = fieldDefinition.outputType.namedType)
            ∨ ((TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
                  = true
                ∧ objectTypeNameBool schema fieldDefinition.outputType.namedType = false))
          ∧ schema.typeIncludesObjectBool
              fieldDefinition.outputType.namedType selectedRuntime
            = true
          ∧ SelectedFieldSpineRuntimeValid schema
              fieldDefinition.outputType.namedType selectedRuntime tail) := by
  intro hvalid hparentObject hlookup hselected
  cases hvalid with
  | objectLeaf hspineObject hspineLookup hleaf =>
      rename_i responseName spineFieldName spineArguments
        spineFieldDefinition
      by_cases hmatch :
          spineFieldName = fieldName
            ∧ Argument.argumentsEquivalent arguments spineArguments
      · simp [selectedObservableFieldSpineNext?, hmatch] at hselected
      · simp [selectedObservableFieldSpineNext?, hmatch] at hselected
  | objectChild hspineObject hspineLookup hcomposite hchildValid =>
      rename_i childRuntimeType responseName spineFieldName spineArguments
        spineFieldDefinition childSpine
      by_cases hmatch :
          spineFieldName = fieldName
            ∧ Argument.argumentsEquivalent arguments spineArguments
      · have hfieldEq : spineFieldName = fieldName := hmatch.1
        subst spineFieldName
        have hdefinitionEq : spineFieldDefinition = fieldDefinition := by
          rw [hlookup] at hspineLookup
          exact (Option.some.inj hspineLookup).symm
        subst spineFieldDefinition
        simp [selectedObservableFieldSpineNext?, hmatch] at hselected
        rcases hselected with ⟨hruntimeEq, htailEq⟩
        subst selectedRuntime
        subst tail
        have hinclude :
            schema.typeIncludesObjectBool
              fieldDefinition.outputType.namedType childRuntimeType = true :=
          selectedFieldSpineRuntimeValid_typeIncludes hchildValid
        by_cases houtputObject :
            objectTypeNameBool schema
              fieldDefinition.outputType.namedType = true
        · have hruntimeOutput :
              childRuntimeType = fieldDefinition.outputType.namedType :=
            typeIncludesObjectBool_eq_of_objectTypeNameBool_true schema
              houtputObject hinclude
          subst childRuntimeType
          exact
            ⟨Or.inl ⟨houtputObject, rfl⟩,
              typeIncludesObjectBool_self_of_objectTypeNameBool schema
                houtputObject,
              hchildValid⟩
        · have houtputNonObject :
              objectTypeNameBool schema
                fieldDefinition.outputType.namedType = false := by
            cases h :
                objectTypeNameBool schema
                  fieldDefinition.outputType.namedType <;>
              simp [h] at houtputObject ⊢
          exact
            ⟨Or.inr ⟨hcomposite, houtputNonObject⟩,
              hinclude, hchildValid⟩
      · simp [selectedObservableFieldSpineNext?, hmatch] at hselected
  | abstractRuntime hnonObject _hruntimeObject _hinclude _hchildValid =>
      rw [hparentObject] at hnonObject
      simp at hnonObject

theorem selectedFieldSpineRuntimeValid_no_leaf_selectedNext_of_composite
    {schema : Schema} {parentType runtimeType fieldName : Name}
    {arguments : List Argument}
    {spine tail : List NormalSelectionSetObservableFieldStep}
    {fieldDefinition : FieldDefinition}
    : SelectedFieldSpineRuntimeValid schema parentType runtimeType spine
      -> objectTypeNameBool schema parentType = true
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> selectedObservableFieldSpineNext? fieldName arguments spine = some (none, tail)
      -> False := by
  intro hvalid hparentObject hlookup hcomposite hselected
  cases hvalid with
  | objectLeaf hspineObject hspineLookup hleaf =>
      rename_i responseName spineFieldName spineArguments
        spineFieldDefinition
      by_cases hmatch :
          spineFieldName = fieldName
            ∧ Argument.argumentsEquivalent arguments spineArguments
      · have hfieldEq : spineFieldName = fieldName := hmatch.1
        subst spineFieldName
        have hdefinitionEq : spineFieldDefinition = fieldDefinition := by
          rw [hlookup] at hspineLookup
          exact (Option.some.inj hspineLookup).symm
        subst spineFieldDefinition
        rw [hcomposite] at hleaf
        simp at hleaf
      · simp [selectedObservableFieldSpineNext?, hmatch] at hselected
  | objectChild hspineObject hspineLookup hcompositeSpine hchildValid =>
      rename_i childRuntimeType responseName spineFieldName spineArguments
        spineFieldDefinition childSpine
      by_cases hmatch :
          spineFieldName = fieldName
            ∧ Argument.argumentsEquivalent arguments spineArguments
      · simp [selectedObservableFieldSpineNext?, hmatch] at hselected
      · simp [selectedObservableFieldSpineNext?, hmatch] at hselected
  | abstractRuntime hnonObject _hruntimeObject _hinclude _hchildValid =>
      rw [hparentObject] at hnonObject
      simp at hnonObject

theorem selectedFieldSpineRuntimeValid_tailForRuntime_of_objectOutput
    {schema : Schema} {parentType runtimeType fieldName : Name}
    {arguments : List Argument}
    {spine : List NormalSelectionSetObservableFieldStep}
    {fieldDefinition : FieldDefinition}
    : SelectedFieldSpineRuntimeValid schema parentType runtimeType spine
      -> objectTypeNameBool schema parentType = true
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> objectTypeNameBool schema fieldDefinition.outputType.namedType = true
      -> selectedObservableFieldSpineTailForRuntime
              fieldDefinition.outputType.namedType fieldName arguments spine
            = []
          ∨ SelectedFieldSpineRuntimeValid schema
              fieldDefinition.outputType.namedType
              fieldDefinition.outputType.namedType
              (selectedObservableFieldSpineTailForRuntime
                fieldDefinition.outputType.namedType fieldName arguments
                spine) := by
  intro hvalid hparentObject hlookup houtputObject
  cases hselected :
      selectedObservableFieldSpineNext? fieldName arguments spine with
  | none =>
      exact Or.inl (by
        simp [selectedObservableFieldSpineTailForRuntime, hselected])
  | some selected =>
      rcases selected with ⟨maybeRuntime, tail⟩
      cases maybeRuntime with
      | none =>
          exact Or.inl (by
            simp [selectedObservableFieldSpineTailForRuntime, hselected])
      | some selectedRuntime =>
          rcases
              selectedFieldSpineRuntimeValid_child_of_selectedNext
                hvalid hparentObject hlookup hselected with
            ⟨hruntimeCase, _hinclude, hchildValid⟩
          rcases hruntimeCase with hobjectRuntime | habstractRuntime
          · rcases hobjectRuntime with ⟨_hobject, hruntimeEq⟩
            subst selectedRuntime
            exact Or.inr (by
              simpa [selectedObservableFieldSpineTailForRuntime,
                hselected])
          · rcases habstractRuntime with ⟨_hcomposite, hnonObject⟩
            rw [houtputObject] at hnonObject
            simp at hnonObject

theorem fieldPairSelectedPathProbeResolvers_left_root
    (schema : Schema)
    (leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (targetParent leftField rightField : Name)
    (leftArguments rightArguments arguments : List Argument)
    (leftRuntime rightRuntime : Name)
    (fieldDefinition : FieldDefinition)
    : Argument.argumentsEquivalent arguments leftArguments
      -> schema.lookupField targetParent leftField = some fieldDefinition
      -> (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
            rightInitialSelectionSet leftInitialSpine rightInitialSpine
            targetParent leftField rightField leftArguments rightArguments
            leftRuntime rightRuntime).resolve
            targetParent leftField arguments
            (.object targetParent FieldPairSelectedPathProbeRef.root)
          = some
              (objectProbeResolverValueWithRuntime leftRuntime
                (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                  leftInitialSelectionSet leftInitialSpine)
                fieldDefinition.outputType) := by
  intro harguments hlookup
  classical
  have htarget :
      fieldProbeTarget targetParent leftField leftArguments targetParent
        leftField arguments := by
    exact ⟨rfl, rfl, harguments⟩
  simp [fieldPairSelectedPathProbeResolvers,
    fieldPairSelectedPathProbeResolve, hlookup, htarget]

theorem fieldPairSelectedPathProbeResolvers_right_root_of_not_left
    (schema : Schema)
    (leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (targetParent leftField rightField : Name)
    (leftArguments rightArguments arguments : List Argument)
    (leftRuntime rightRuntime : Name)
    (fieldDefinition : FieldDefinition)
    : ¬ fieldProbeTarget targetParent leftField leftArguments targetParent
          rightField arguments
      -> Argument.argumentsEquivalent arguments rightArguments
      -> schema.lookupField targetParent rightField = some fieldDefinition
      -> (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
            rightInitialSelectionSet leftInitialSpine rightInitialSpine
            targetParent leftField rightField leftArguments rightArguments
            leftRuntime rightRuntime).resolve
            targetParent rightField arguments
            (.object targetParent FieldPairSelectedPathProbeRef.root)
          = some
              (objectProbeResolverValueWithRuntime rightRuntime
                (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                  rightInitialSelectionSet rightInitialSpine)
                fieldDefinition.outputType) := by
  intro hnotLeft harguments hlookup
  classical
  have hright :
      fieldProbeTarget targetParent rightField rightArguments targetParent
        rightField arguments := by
    exact ⟨rfl, rfl, harguments⟩
  simp [fieldPairSelectedPathProbeResolvers,
    fieldPairSelectedPathProbeResolve, hlookup, hnotLeft, hright]

theorem executeField_fieldPairOrDeepSuccess_selectedPathProbe_left_root_response
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues)
    (fuel : Nat) (targetParent leftField rightField responseName : Name)
    (leftArguments rightArguments arguments : List Argument)
    (leftRuntime rightRuntime : Name)
    (childSelectionSet : List Selection) (fieldDefinition : FieldDefinition)
    : Argument.argumentsEquivalent arguments leftArguments
      -> schema.lookupField targetParent leftField = some fieldDefinition
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType leftRuntime
          = true
      -> Execution.executeField schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet leftInitialSpine rightInitialSpine
                targetParent leftField rightField leftArguments rightArguments
                leftRuntime rightRuntime)
              targetParent leftField rightField leftArguments rightArguments)
            variableValues (fuel + leafProbeFuel fieldDefinition.outputType + 1)
            (projectionRootResolverValue
              (.object targetParent FieldPairSelectedPathProbeRef.root))
            responseName
            [{
              parentType := targetParent
              responseName := responseName
              fieldName := leftField
              arguments := arguments
              selectionSet := childSelectionSet
            }]
          = Execution.singleFieldResult responseName
              (wrapTypeRefSelectionSetResult fieldDefinition.outputType
                (Execution.selectionSetResultToResponse
                  (Execution.executeCollectedFields schema
                    (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                      (fieldPairSelectedPathProbeResolvers schema
                        leftInitialSelectionSet rightInitialSelectionSet
                        leftInitialSpine rightInitialSpine targetParent leftField
                        rightField leftArguments rightArguments leftRuntime
                        rightRuntime)
                      targetParent leftField rightField leftArguments
                      rightArguments)
                    variableValues fuel
                    (projectionTargetResolverValue
                      (.object leftRuntime
                        (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                          leftInitialSelectionSet leftInitialSpine)))
                    (Execution.collectFields schema variableValues leftRuntime
                      (projectionTargetResolverValue
                        (.object leftRuntime
                          (FieldPairSelectedPathProbeRef.target
                            FieldPairProbeTag.left leftInitialSelectionSet
                            leftInitialSpine)))
                      childSelectionSet)))) := by
  intro harguments hlookup hinclude
  let base :=
    fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
      rightInitialSelectionSet leftInitialSpine rightInitialSpine
      targetParent leftField rightField leftArguments rightArguments
      leftRuntime rightRuntime
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet base
      targetParent leftField rightField leftArguments rightArguments
  have hbase :
      base.resolve targetParent leftField arguments
          (.object targetParent FieldPairSelectedPathProbeRef.root)
      =
      some
        (objectProbeResolverValueWithRuntime leftRuntime
          (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
            leftInitialSelectionSet leftInitialSpine)
          fieldDefinition.outputType) :=
    fieldPairSelectedPathProbeResolvers_left_root schema
      leftInitialSelectionSet rightInitialSelectionSet leftInitialSpine
      rightInitialSpine targetParent leftField rightField leftArguments
      rightArguments arguments leftRuntime rightRuntime fieldDefinition
      harguments hlookup
  have hresolve :
      resolvers.resolve targetParent leftField arguments
          (projectionRootResolverValue
            (.object targetParent FieldPairSelectedPathProbeRef.root))
      =
      some
        (objectProbeResolverValueWithRuntime leftRuntime
          (ProjectionResolverRef.target
            (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
              leftInitialSelectionSet leftInitialSpine))
          fieldDefinition.outputType) := by
    have hroot :=
      fieldPairOrDeepSuccessResolvers_left_root schema rootSelectionSet base
        targetParent leftField rightField leftArguments rightArguments
        arguments
        (.object targetParent FieldPairSelectedPathProbeRef.root)
        harguments
    rw [hroot, hbase]
    simp [Option.map,
      projectionTargetResolverValue_objectProbeResolverValueWithRuntime]
  have hfield :=
    executeField_objectProbeWithRuntime_response schema resolvers
      variableValues fuel
      (projectionRootResolverValue
        (.object targetParent FieldPairSelectedPathProbeRef.root))
      responseName targetParent leftField arguments childSelectionSet
      fieldDefinition leftRuntime
      (ProjectionResolverRef.target
        (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
          leftInitialSelectionSet leftInitialSpine))
      hlookup hresolve hinclude
  simpa [base, resolvers, projectionTargetResolverValue,
    projectionResolverValue] using hfield

theorem executeField_fieldPairOrDeepSuccess_selectedPathProbe_right_root_response_of_not_left
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField responseName : Name)
    (leftArguments rightArguments arguments : List Argument)
    (leftRuntime rightRuntime : Name) (childSelectionSet : List Selection)
    (fieldDefinition : FieldDefinition)
    : ¬ fieldProbeTarget targetParent leftField leftArguments targetParent
          rightField arguments
      -> Argument.argumentsEquivalent arguments rightArguments
      -> schema.lookupField targetParent rightField = some fieldDefinition
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType rightRuntime
          = true
      -> Execution.executeField schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet leftInitialSpine rightInitialSpine
                targetParent leftField rightField leftArguments rightArguments
                leftRuntime rightRuntime)
              targetParent leftField rightField leftArguments rightArguments)
            variableValues (fuel + leafProbeFuel fieldDefinition.outputType + 1)
            (projectionRootResolverValue
              (.object targetParent FieldPairSelectedPathProbeRef.root))
            responseName
            [{
              parentType := targetParent
              responseName := responseName
              fieldName := rightField
              arguments := arguments
              selectionSet := childSelectionSet
            }]
          = Execution.singleFieldResult responseName
              (wrapTypeRefSelectionSetResult fieldDefinition.outputType
                (Execution.selectionSetResultToResponse
                  (Execution.executeCollectedFields schema
                    (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                      (fieldPairSelectedPathProbeResolvers schema
                        leftInitialSelectionSet rightInitialSelectionSet
                        leftInitialSpine rightInitialSpine targetParent leftField
                        rightField leftArguments rightArguments leftRuntime
                        rightRuntime)
                      targetParent leftField rightField leftArguments
                      rightArguments)
                    variableValues fuel
                    (projectionTargetResolverValue
                      (.object rightRuntime
                        (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                          rightInitialSelectionSet rightInitialSpine)))
                    (Execution.collectFields schema variableValues rightRuntime
                      (projectionTargetResolverValue
                        (.object rightRuntime
                          (FieldPairSelectedPathProbeRef.target
                            FieldPairProbeTag.right rightInitialSelectionSet
                            rightInitialSpine)))
                      childSelectionSet)))) := by
  intro hnotLeft harguments hlookup hinclude
  let base :=
    fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
      rightInitialSelectionSet leftInitialSpine rightInitialSpine
      targetParent leftField rightField leftArguments rightArguments
      leftRuntime rightRuntime
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet base
      targetParent leftField rightField leftArguments rightArguments
  have hbase :
      base.resolve targetParent rightField arguments
          (.object targetParent FieldPairSelectedPathProbeRef.root)
      =
      some
        (objectProbeResolverValueWithRuntime rightRuntime
          (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
            rightInitialSelectionSet rightInitialSpine)
          fieldDefinition.outputType) :=
    fieldPairSelectedPathProbeResolvers_right_root_of_not_left schema
      leftInitialSelectionSet rightInitialSelectionSet leftInitialSpine
      rightInitialSpine targetParent leftField rightField leftArguments
      rightArguments arguments leftRuntime rightRuntime fieldDefinition
      hnotLeft harguments hlookup
  have hresolve :
      resolvers.resolve targetParent rightField arguments
          (projectionRootResolverValue
            (.object targetParent FieldPairSelectedPathProbeRef.root))
      =
      some
        (objectProbeResolverValueWithRuntime rightRuntime
          (ProjectionResolverRef.target
            (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
              rightInitialSelectionSet rightInitialSpine))
          fieldDefinition.outputType) := by
    have hroot :=
      fieldPairOrDeepSuccessResolvers_right_root schema rootSelectionSet base
        targetParent leftField rightField leftArguments rightArguments
        arguments
        (.object targetParent FieldPairSelectedPathProbeRef.root)
        harguments
    rw [hroot, hbase]
    simp [Option.map,
      projectionTargetResolverValue_objectProbeResolverValueWithRuntime]
  have hfield :=
    executeField_objectProbeWithRuntime_response schema resolvers
      variableValues fuel
      (projectionRootResolverValue
        (.object targetParent FieldPairSelectedPathProbeRef.root))
      responseName targetParent rightField arguments childSelectionSet
      fieldDefinition rightRuntime
      (ProjectionResolverRef.target
        (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
          rightInitialSelectionSet rightInitialSpine))
      hlookup hresolve hinclude
  simpa [base, resolvers, projectionTargetResolverValue,
    projectionResolverValue] using hfield

theorem executeField_fieldPairOrDeepSuccess_selectedPathProbe_other_root_ok_of_deepSuccessWithRef_ok
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (parentFuel : Nat)
    (targetParent leftField rightField : Name)
    (leftArguments rightArguments arguments : List Argument)
    (leftRuntime rightRuntime : Name) (responseName fieldName : Name)
    (childSelectionSet : List Selection) (responseValue : Execution.ResponseValue)
    (fieldErrors : Nat)
    : ¬ fieldPairProjectionTarget targetParent leftField rightField
          leftArguments rightArguments targetParent fieldName arguments
      -> Execution.executeField schema
            (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet
              (ProjectionResolverRef.filler
                : ProjectionResolverRef FieldPairSelectedPathProbeRef))
            variableValues parentFuel
            (projectionRootResolverValue
              (.object targetParent FieldPairSelectedPathProbeRef.root))
            responseName
            [{
              parentType := targetParent,
              responseName := responseName,
              fieldName := fieldName,
              arguments := arguments,
              selectionSet := childSelectionSet
            }]
          = .ok ([(responseName, responseValue)], fieldErrors)
      -> Execution.executeField schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet leftInitialSpine rightInitialSpine
                targetParent leftField rightField leftArguments rightArguments
                leftRuntime rightRuntime)
              targetParent leftField rightField leftArguments rightArguments)
            variableValues parentFuel
            (projectionRootResolverValue
              (.object targetParent FieldPairSelectedPathProbeRef.root))
            responseName
            [{
              parentType := targetParent,
              responseName := responseName,
              fieldName := fieldName,
              arguments := arguments,
              selectionSet := childSelectionSet
            }]
          = .ok ([(responseName, responseValue)], fieldErrors) := by
  intro hnotProjection hdeep
  simp only [projectionRootResolverValue, projectionResolverValue] at hdeep ⊢
  rw [executeField_fieldPairOrDeepSuccessResolvers_other_root_eq_deepSuccessWithRef
    schema rootSelectionSet
    (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
      rightInitialSelectionSet leftInitialSpine rightInitialSpine
      targetParent leftField rightField leftArguments rightArguments
      leftRuntime rightRuntime)
    variableValues targetParent leftField rightField targetParent
    fieldName targetParent responseName leftArguments rightArguments
    arguments FieldPairSelectedPathProbeRef.root childSelectionSet
    hnotProjection parentFuel]
  exact hdeep

theorem selectionSetOtherFieldsExecuteOk_fieldPairOrDeepSuccess_selectedPathProbe_of_deepSuccessWithRef_ok
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (parentFuel : Nat)
    (targetParent leftField rightField : Name)
    (leftArguments rightArguments : List Argument) (leftRuntime rightRuntime : Name)
    (selectionSet : List Selection)
    : (∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
        -> ∃ responseValue fieldErrors,
            Execution.executeField schema
              (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet
                (ProjectionResolverRef.filler
                  : ProjectionResolverRef FieldPairSelectedPathProbeRef))
              variableValues parentFuel
              (projectionRootResolverValue
                (.object targetParent FieldPairSelectedPathProbeRef.root))
              responseName
              [{
                parentType := targetParent,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := childSelectionSet
              }]
            = .ok ([(responseName, responseValue)], fieldErrors))
      -> ∀ responseName fieldName arguments directives childSelectionSet,
          Selection.field responseName fieldName arguments directives childSelectionSet
            ∈ selectionSet
          -> ¬ fieldPairProjectionTarget targetParent leftField rightField
                leftArguments rightArguments targetParent fieldName arguments
          -> ∃ responseValue fieldErrors,
              Execution.executeField schema
                (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                  (fieldPairSelectedPathProbeResolvers schema
                    leftInitialSelectionSet rightInitialSelectionSet
                    leftInitialSpine rightInitialSpine targetParent leftField
                    rightField leftArguments rightArguments leftRuntime
                    rightRuntime)
                  targetParent leftField rightField leftArguments
                  rightArguments)
                variableValues parentFuel
                (projectionRootResolverValue
                  (.object targetParent FieldPairSelectedPathProbeRef.root))
                responseName
                [{
                  parentType := targetParent,
                  responseName := responseName,
                  fieldName := fieldName,
                  arguments := arguments,
                  selectionSet := childSelectionSet
                }]
              = .ok ([(responseName, responseValue)], fieldErrors) := by
  intro hdeep responseName fieldName arguments directives childSelectionSet
    hmem hnotProjection
  rcases hdeep responseName fieldName arguments directives childSelectionSet
      hmem with
    ⟨responseValue, fieldErrors, hdeepOk⟩
  exact
    ⟨responseValue, fieldErrors,
      executeField_fieldPairOrDeepSuccess_selectedPathProbe_other_root_ok_of_deepSuccessWithRef_ok
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftInitialSpine rightInitialSpine
        variableValues parentFuel targetParent leftField rightField
        leftArguments rightArguments arguments leftRuntime rightRuntime
        responseName fieldName childSelectionSet responseValue fieldErrors
        hnotProjection hdeepOk⟩

theorem executeField_fieldPairOrDeepSuccess_selectedPathProbe_left_root_ok_of_child_object_response_fuel_ge
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (parentFuel : Nat)
    (targetParent leftField rightField responseName : Name)
    (leftArguments rightArguments arguments : List Argument)
    (leftRuntime rightRuntime : Name) (childSelectionSet : List Selection)
    (fieldDefinition : FieldDefinition)
    (childFields : List (Name × Execution.ResponseValue)) (childErrors : Nat)
    : Argument.argumentsEquivalent arguments leftArguments
      -> schema.lookupField targetParent leftField = some fieldDefinition
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType leftRuntime
          = true
      -> leafProbeFuel fieldDefinition.outputType ≤ parentFuel
      -> Execution.executeSelectionSetAsResponse schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet leftInitialSpine rightInitialSpine
                targetParent leftField rightField leftArguments rightArguments
                leftRuntime rightRuntime)
              targetParent leftField rightField leftArguments rightArguments)
            variableValues (parentFuel - leafProbeFuel fieldDefinition.outputType)
            leftRuntime
            (projectionTargetResolverValue
              (.object leftRuntime
                (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                  leftInitialSelectionSet leftInitialSpine)))
            childSelectionSet
          = ({ data := Execution.ResponseValue.object childFields, errors := childErrors }
              : Execution.Response)
      -> ∃ responseValue fieldErrors,
          Execution.executeField schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet leftInitialSpine rightInitialSpine
                targetParent leftField rightField leftArguments rightArguments
                leftRuntime rightRuntime)
              targetParent leftField rightField leftArguments rightArguments)
            variableValues (parentFuel + 1)
            (projectionRootResolverValue
              (.object targetParent FieldPairSelectedPathProbeRef.root))
            responseName
            [{
              parentType := targetParent
              responseName := responseName
              fieldName := leftField
              arguments := arguments
              selectionSet := childSelectionSet
            }]
          = .ok ([(responseName, responseValue)], fieldErrors) := by
  intro harguments hlookup hinclude hfuel hchildResponse
  rcases
      wrapTypeRefSelectionSetResult_ok_nonNull_of_object_response
        fieldDefinition.outputType childFields childErrors with
    ⟨responseValue, fieldErrors, hwrapped, _hresponseNonNull⟩
  refine ⟨responseValue, fieldErrors, ?_⟩
  have hchildRaw :
      Execution.selectionSetResultToResponse
        (Execution.executeCollectedFields schema
          (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
            (fieldPairSelectedPathProbeResolvers schema
              leftInitialSelectionSet rightInitialSelectionSet
              leftInitialSpine rightInitialSpine targetParent leftField
              rightField leftArguments rightArguments leftRuntime
              rightRuntime)
            targetParent leftField rightField leftArguments rightArguments)
          variableValues
          (parentFuel - leafProbeFuel fieldDefinition.outputType)
          (projectionTargetResolverValue
            (.object leftRuntime
              (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                leftInitialSelectionSet leftInitialSpine)))
          (Execution.collectFields schema variableValues leftRuntime
            (projectionTargetResolverValue
              (.object leftRuntime
                (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.left
                  leftInitialSelectionSet leftInitialSpine)))
            childSelectionSet))
      =
      ({ data := Execution.ResponseValue.object childFields,
         errors := childErrors } :
        Execution.Response) := by
    simpa [Execution.executeSelectionSetAsResponse, Execution.executeSelectionSet,
      Execution.executeRootSelectionSet] using hchildResponse
  have hfield :=
    executeField_fieldPairOrDeepSuccess_selectedPathProbe_left_root_response
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet leftInitialSpine rightInitialSpine
      variableValues
      (parentFuel - leafProbeFuel fieldDefinition.outputType)
      targetParent leftField rightField responseName leftArguments
      rightArguments arguments leftRuntime rightRuntime childSelectionSet
      fieldDefinition harguments hlookup hinclude
  have hfuelEq :
      parentFuel - leafProbeFuel fieldDefinition.outputType
          + leafProbeFuel fieldDefinition.outputType + 1
        =
      parentFuel + 1 := by
    omega
  simpa [hchildRaw, hwrapped, Execution.singleFieldResult, hfuelEq]
    using hfield

theorem executeField_fieldPairOrDeepSuccess_selectedPathProbe_right_root_ok_of_child_object_response_fuel_ge
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (parentFuel : Nat)
    (targetParent leftField rightField responseName : Name)
    (leftArguments rightArguments arguments : List Argument)
    (leftRuntime rightRuntime : Name) (childSelectionSet : List Selection)
    (fieldDefinition : FieldDefinition)
    (childFields : List (Name × Execution.ResponseValue)) (childErrors : Nat)
    : ¬ fieldProbeTarget targetParent leftField leftArguments targetParent
          rightField arguments
      -> Argument.argumentsEquivalent arguments rightArguments
      -> schema.lookupField targetParent rightField = some fieldDefinition
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType rightRuntime
          = true
      -> leafProbeFuel fieldDefinition.outputType ≤ parentFuel
      -> Execution.executeSelectionSetAsResponse schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet leftInitialSpine rightInitialSpine
                targetParent leftField rightField leftArguments rightArguments
                leftRuntime rightRuntime)
              targetParent leftField rightField leftArguments rightArguments)
            variableValues (parentFuel - leafProbeFuel fieldDefinition.outputType)
            rightRuntime
            (projectionTargetResolverValue
              (.object rightRuntime
                (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                  rightInitialSelectionSet rightInitialSpine)))
            childSelectionSet
          = ({ data := Execution.ResponseValue.object childFields, errors := childErrors }
              : Execution.Response)
      -> ∃ responseValue fieldErrors,
          Execution.executeField schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet leftInitialSpine rightInitialSpine
                targetParent leftField rightField leftArguments rightArguments
                leftRuntime rightRuntime)
              targetParent leftField rightField leftArguments rightArguments)
            variableValues (parentFuel + 1)
            (projectionRootResolverValue
              (.object targetParent FieldPairSelectedPathProbeRef.root))
            responseName
            [{
              parentType := targetParent
              responseName := responseName
              fieldName := rightField
              arguments := arguments
              selectionSet := childSelectionSet
            }]
          = .ok ([(responseName, responseValue)], fieldErrors) := by
  intro hnotLeft harguments hlookup hinclude hfuel hchildResponse
  rcases
      wrapTypeRefSelectionSetResult_ok_nonNull_of_object_response
        fieldDefinition.outputType childFields childErrors with
    ⟨responseValue, fieldErrors, hwrapped, _hresponseNonNull⟩
  refine ⟨responseValue, fieldErrors, ?_⟩
  have hchildRaw :
      Execution.selectionSetResultToResponse
        (Execution.executeCollectedFields schema
          (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
            (fieldPairSelectedPathProbeResolvers schema
              leftInitialSelectionSet rightInitialSelectionSet
              leftInitialSpine rightInitialSpine targetParent leftField
              rightField leftArguments rightArguments leftRuntime
              rightRuntime)
            targetParent leftField rightField leftArguments rightArguments)
          variableValues
          (parentFuel - leafProbeFuel fieldDefinition.outputType)
          (projectionTargetResolverValue
            (.object rightRuntime
              (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                rightInitialSelectionSet rightInitialSpine)))
          (Execution.collectFields schema variableValues rightRuntime
            (projectionTargetResolverValue
              (.object rightRuntime
                (FieldPairSelectedPathProbeRef.target FieldPairProbeTag.right
                  rightInitialSelectionSet rightInitialSpine)))
            childSelectionSet))
      =
      ({ data := Execution.ResponseValue.object childFields,
         errors := childErrors } :
        Execution.Response) := by
    simpa [Execution.executeSelectionSetAsResponse, Execution.executeSelectionSet,
      Execution.executeRootSelectionSet] using hchildResponse
  have hfield :=
    executeField_fieldPairOrDeepSuccess_selectedPathProbe_right_root_response_of_not_left
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet leftInitialSpine rightInitialSpine
      variableValues
      (parentFuel - leafProbeFuel fieldDefinition.outputType)
      targetParent leftField rightField responseName leftArguments
      rightArguments arguments leftRuntime rightRuntime childSelectionSet
      fieldDefinition hnotLeft harguments hlookup hinclude
  have hfuelEq :
      parentFuel - leafProbeFuel fieldDefinition.outputType
          + leafProbeFuel fieldDefinition.outputType + 1
        =
      parentFuel + 1 := by
    omega
  simpa [hchildRaw, hwrapped, Execution.singleFieldResult, hfuelEq]
    using hfield

theorem selectionSetFieldsExecuteOk_fieldPairOrDeepSuccess_selectedPathProbe_of_field_cases
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (leftInitialSpine rightInitialSpine : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (parentFuel : Nat)
    (targetParent leftField rightField : Name)
    (leftArguments rightArguments : List Argument) (leftRuntime rightRuntime : Name)
    (leftFieldDefinition rightFieldDefinition : FieldDefinition)
    (selectionSet : List Selection)
    : schema.lookupField targetParent leftField = some leftFieldDefinition
      -> schema.lookupField targetParent rightField = some rightFieldDefinition
      -> schema.typeIncludesObjectBool
            leftFieldDefinition.outputType.namedType leftRuntime
          = true
      -> schema.typeIncludesObjectBool
            rightFieldDefinition.outputType.namedType rightRuntime
          = true
      -> leafProbeFuel leftFieldDefinition.outputType ≤ parentFuel
      -> leafProbeFuel rightFieldDefinition.outputType ≤ parentFuel
      -> (∀ responseName arguments directives childSelectionSet,
            Selection.field responseName leftField arguments directives childSelectionSet
              ∈ selectionSet
            -> Argument.argumentsEquivalent arguments leftArguments
            -> ∃ childFields childErrors,
                Execution.executeSelectionSetAsResponse schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairSelectedPathProbeResolvers schema
                      leftInitialSelectionSet rightInitialSelectionSet
                      leftInitialSpine rightInitialSpine targetParent leftField
                      rightField leftArguments rightArguments leftRuntime
                      rightRuntime)
                    targetParent leftField rightField leftArguments
                    rightArguments)
                  variableValues
                  (parentFuel - leafProbeFuel leftFieldDefinition.outputType)
                  leftRuntime
                  (projectionTargetResolverValue
                    (.object leftRuntime
                      (FieldPairSelectedPathProbeRef.target
                        FieldPairProbeTag.left leftInitialSelectionSet
                        leftInitialSpine)))
                  childSelectionSet
                = ({
                      data := Execution.ResponseValue.object childFields,
                      errors := childErrors
                    }
                    : Execution.Response))
      -> (∀ responseName arguments directives childSelectionSet,
            Selection.field responseName rightField arguments directives childSelectionSet
              ∈ selectionSet
            -> Argument.argumentsEquivalent arguments rightArguments
            -> ∃ childFields childErrors,
                Execution.executeSelectionSetAsResponse schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairSelectedPathProbeResolvers schema
                      leftInitialSelectionSet rightInitialSelectionSet
                      leftInitialSpine rightInitialSpine targetParent leftField
                      rightField leftArguments rightArguments leftRuntime
                      rightRuntime)
                    targetParent leftField rightField leftArguments
                    rightArguments)
                  variableValues
                  (parentFuel - leafProbeFuel rightFieldDefinition.outputType)
                  rightRuntime
                  (projectionTargetResolverValue
                    (.object rightRuntime
                      (FieldPairSelectedPathProbeRef.target
                        FieldPairProbeTag.right rightInitialSelectionSet
                        rightInitialSpine)))
                  childSelectionSet
                = ({
                      data := Execution.ResponseValue.object childFields,
                      errors := childErrors
                    }
                    : Execution.Response))
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ selectionSet
            -> ¬ fieldPairProjectionTarget targetParent leftField rightField
                  leftArguments rightArguments targetParent fieldName arguments
            -> ∃ responseValue fieldErrors,
                Execution.executeField schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairSelectedPathProbeResolvers schema
                      leftInitialSelectionSet rightInitialSelectionSet
                      leftInitialSpine rightInitialSpine targetParent leftField
                      rightField leftArguments rightArguments leftRuntime
                      rightRuntime)
                    targetParent leftField rightField leftArguments
                    rightArguments)
                  variableValues (parentFuel + 1)
                  (projectionRootResolverValue
                    (.object targetParent FieldPairSelectedPathProbeRef.root))
                  responseName
                  [{
                    parentType := targetParent
                    responseName := responseName
                    fieldName := fieldName
                    arguments := arguments
                    selectionSet := childSelectionSet
                  }]
                = .ok ([(responseName, responseValue)], fieldErrors))
      -> selectionSetFieldsExecuteOk schema
          (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
            (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
              rightInitialSelectionSet leftInitialSpine rightInitialSpine
              targetParent leftField rightField leftArguments rightArguments
              leftRuntime rightRuntime)
            targetParent leftField rightField leftArguments rightArguments)
          variableValues (parentFuel + 1) targetParent
          (projectionRootResolverValue
            (.object targetParent FieldPairSelectedPathProbeRef.root))
          selectionSet := by
  intro hleftLookup hrightLookup hleftInclude hrightInclude hleftFuel
    hrightFuel hleftChildResponse hrightChildResponse hother
  intro responseName fieldName arguments directives childSelectionSet hmem
  by_cases hleftTarget :
      fieldProbeTarget targetParent leftField leftArguments targetParent
        fieldName arguments
  · rcases hleftTarget with ⟨_hparent, hfield, harguments⟩
    subst fieldName
    rcases
        hleftChildResponse responseName arguments directives
          childSelectionSet hmem harguments with
      ⟨childFields, childErrors, hchildResponse⟩
    exact
      executeField_fieldPairOrDeepSuccess_selectedPathProbe_left_root_ok_of_child_object_response_fuel_ge
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet leftInitialSpine rightInitialSpine
        variableValues parentFuel targetParent leftField rightField
        responseName leftArguments rightArguments arguments leftRuntime
        rightRuntime childSelectionSet leftFieldDefinition childFields
        childErrors harguments hleftLookup hleftInclude hleftFuel
        hchildResponse
  · by_cases hrightTarget :
        fieldProbeTarget targetParent rightField rightArguments targetParent
          fieldName arguments
    · rcases hrightTarget with ⟨_hparent, hfield, harguments⟩
      subst fieldName
      have hnotLeft :
          ¬ fieldProbeTarget targetParent leftField leftArguments
            targetParent rightField arguments := by
        intro htarget
        exact hleftTarget htarget
      rcases
          hrightChildResponse responseName arguments directives
            childSelectionSet hmem harguments with
        ⟨childFields, childErrors, hchildResponse⟩
      exact
        executeField_fieldPairOrDeepSuccess_selectedPathProbe_right_root_ok_of_child_object_response_fuel_ge
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet leftInitialSpine rightInitialSpine
          variableValues parentFuel targetParent leftField rightField
          responseName leftArguments rightArguments arguments leftRuntime
          rightRuntime childSelectionSet rightFieldDefinition childFields
          childErrors hnotLeft harguments hrightLookup hrightInclude
          hrightFuel hchildResponse
    · have hnotProjection :
          ¬ fieldPairProjectionTarget targetParent leftField rightField
            leftArguments rightArguments targetParent fieldName arguments := by
        intro hprojection
        rcases hprojection with ⟨_hparent, htarget⟩
        rcases htarget with hleft | hright
        · exact hleftTarget ⟨rfl, hleft.1, hleft.2⟩
        · exact hrightTarget ⟨rfl, hright.1, hright.2⟩
      exact
        hother responseName fieldName arguments directives childSelectionSet
          hmem hnotProjection

theorem fieldPairSelectedPathProbeResolvers_tagged_object
    (schema : Schema)
    (leftInitialSelectionSet rightInitialSelectionSet currentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine spine
      : List NormalSelectionSetObservableFieldStep)
    (targetParent leftField rightField parentType fieldName runtimeType : Name)
    (leftArguments rightArguments arguments : List Argument)
    (leftRuntime rightRuntime : Name)
    (tag : FieldPairProbeTag) (fieldDefinition : FieldDefinition)
    : schema.lookupField parentType fieldName = some fieldDefinition
      -> (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
            rightInitialSelectionSet leftInitialSpine rightInitialSpine
            targetParent leftField rightField leftArguments rightArguments
            leftRuntime rightRuntime).resolve
            parentType fieldName arguments
            (.object runtimeType
              (FieldPairSelectedPathProbeRef.target tag currentSelectionSet spine))
          = some
              (fieldPairSelectedPathProbeHeadResolverValue schema
                currentSelectionSet parentType fieldName arguments tag spine
                fieldDefinition.outputType) := by
  intro hlookup
  simp [fieldPairSelectedPathProbeResolvers,
    fieldPairSelectedPathProbeResolve, hlookup]

theorem fieldPairSelectedPathProbeResolvers_tagged_object_selected_runtime
    (schema : Schema)
    (leftInitialSelectionSet rightInitialSelectionSet currentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine spine tail
      : List NormalSelectionSetObservableFieldStep)
    (targetParent leftField rightField parentType fieldName runtimeType selectedRuntime
      : Name)
    (leftArguments rightArguments arguments : List Argument)
    (leftRuntime rightRuntime : Name)
    (tag : FieldPairProbeTag) (fieldDefinition : FieldDefinition)
    : schema.lookupField parentType fieldName = some fieldDefinition
      -> selectedObservableFieldSpineNext? fieldName arguments spine
          = some (some selectedRuntime, tail)
      -> ((objectTypeNameBool schema fieldDefinition.outputType.namedType = true
            ∧ selectedRuntime = fieldDefinition.outputType.namedType)
          ∨ ((TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
                = true
              ∧ objectTypeNameBool schema fieldDefinition.outputType.namedType = false))
      -> (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
            rightInitialSelectionSet leftInitialSpine rightInitialSpine
            targetParent leftField rightField leftArguments rightArguments
            leftRuntime rightRuntime).resolve
            parentType fieldName arguments
            (.object runtimeType
              (FieldPairSelectedPathProbeRef.target tag currentSelectionSet spine))
          = some
              (objectProbeResolverValueWithRuntime selectedRuntime
                (FieldPairSelectedPathProbeRef.target tag
                  (fieldPairPathLocalNextSelectionSet schema parentType
                    selectedRuntime fieldName arguments currentSelectionSet)
                  tail)
                fieldDefinition.outputType) := by
  intro hlookup hselected hcase
  rw [fieldPairSelectedPathProbeResolvers_tagged_object schema
    leftInitialSelectionSet rightInitialSelectionSet currentSelectionSet
    leftInitialSpine rightInitialSpine spine targetParent leftField
    rightField parentType fieldName runtimeType leftArguments
    rightArguments arguments leftRuntime rightRuntime tag fieldDefinition
    hlookup]
  rw [
    fieldPairSelectedPathProbeHeadResolverValue_selected_eq_objectProbeResolverValueWithRuntime
      schema currentSelectionSet parentType fieldName selectedRuntime
      arguments tag spine tail fieldDefinition.outputType hselected hcase]

theorem fieldPairSelectedPathProbeHeadResolverValue_leaf_eq_leafProbeResolverValue
    (schema : Schema) (currentSelectionSet : List Selection)
    (parentType fieldName : Name) (arguments : List Argument)
    (tag : FieldPairProbeTag)
    (spine : List NormalSelectionSetObservableFieldStep)
    : ∀ outputType,
        (TypeRef.named outputType.namedType).isCompositeBool schema = false
        -> fieldPairSelectedPathProbeHeadResolverValue schema
              currentSelectionSet parentType fieldName arguments tag spine
              outputType
            = leafProbeResolverValue outputType tag.scalar
  | .named typeName, hleaf => by
      have hleafNamed :
          (TypeRef.named typeName).isCompositeBool schema = false := by
        simpa [TypeRef.namedType] using hleaf
      simp [fieldPairSelectedPathProbeHeadResolverValue,
        leafProbeResolverValue, hleafNamed]
  | .list inner, hleaf => by
      have hinner :=
        fieldPairSelectedPathProbeHeadResolverValue_leaf_eq_leafProbeResolverValue
          schema currentSelectionSet parentType fieldName arguments tag
          spine inner
          (by simpa [TypeRef.namedType] using hleaf)
      simp [fieldPairSelectedPathProbeHeadResolverValue,
        leafProbeResolverValue, hinner]
  | .nonNull inner, hleaf => by
      exact
        fieldPairSelectedPathProbeHeadResolverValue_leaf_eq_leafProbeResolverValue
          schema currentSelectionSet parentType fieldName arguments tag
          spine inner
          (by simpa [TypeRef.namedType] using hleaf)

theorem executeField_fieldPairSelectedPathProbe_tagged_object_leaf (schema : Schema)
    (leftInitialSelectionSet rightInitialSelectionSet currentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine spine
      : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField parentType fieldName sourceRuntimeType responseName
      : Name)
    (leftArguments rightArguments arguments : List Argument)
    (leftRuntime rightRuntime : Name) (tag : FieldPairProbeTag)
    (childSelectionSet : List Selection) (fieldDefinition : FieldDefinition)
    : schema.lookupField parentType fieldName = some fieldDefinition
      -> leafProbeFuel fieldDefinition.outputType ≤ fuel
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> Execution.executeField schema
            (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
              rightInitialSelectionSet leftInitialSpine rightInitialSpine
              targetParent leftField rightField leftArguments rightArguments
              leftRuntime rightRuntime)
            variableValues (fuel + 1)
            (.object sourceRuntimeType
              (FieldPairSelectedPathProbeRef.target tag currentSelectionSet spine))
            responseName
            [{
              parentType := parentType
              responseName := responseName
              fieldName := fieldName
              arguments := arguments
              selectionSet := childSelectionSet
            }]
          = .ok
              (
                [(
                  responseName,
                  leafProbeResponseValue fieldDefinition.outputType tag.scalar
                )],
                0
              ) := by
  intro hlookup hfuel hleaf
  have hresolve :
      (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
          rightInitialSelectionSet leftInitialSpine rightInitialSpine
          targetParent leftField rightField leftArguments rightArguments
          leftRuntime rightRuntime).resolve
        parentType fieldName arguments
        (.object sourceRuntimeType
          (FieldPairSelectedPathProbeRef.target tag currentSelectionSet
            spine))
      =
      some
        (leafProbeResolverValue
          (ObjectRef := FieldPairSelectedPathProbeRef)
          fieldDefinition.outputType tag.scalar) := by
    rw [fieldPairSelectedPathProbeResolvers_tagged_object schema
      leftInitialSelectionSet rightInitialSelectionSet currentSelectionSet
      leftInitialSpine rightInitialSpine spine targetParent leftField
      rightField parentType fieldName sourceRuntimeType leftArguments
      rightArguments arguments leftRuntime rightRuntime tag fieldDefinition
      hlookup]
    rw [
      fieldPairSelectedPathProbeHeadResolverValue_leaf_eq_leafProbeResolverValue
        schema currentSelectionSet parentType fieldName arguments tag spine
        fieldDefinition.outputType hleaf]
  exact
    executeField_leafProbe_singleton_of_resolve_fuel_ge schema
      (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
        rightInitialSelectionSet leftInitialSpine rightInitialSpine
        targetParent leftField rightField leftArguments rightArguments
        leftRuntime rightRuntime)
      variableValues fuel
      (.object sourceRuntimeType
        (FieldPairSelectedPathProbeRef.target tag currentSelectionSet
          spine))
      responseName parentType fieldName arguments childSelectionSet
      fieldDefinition tag.scalar hlookup hresolve hfuel hleaf

theorem executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_leaf
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet currentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine spine
      : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField parentType fieldName sourceRuntimeType responseName
      : Name)
    (leftArguments rightArguments arguments : List Argument)
    (leftRuntime rightRuntime : Name) (tag : FieldPairProbeTag)
    (childSelectionSet : List Selection) (fieldDefinition : FieldDefinition)
    : schema.lookupField parentType fieldName = some fieldDefinition
      -> leafProbeFuel fieldDefinition.outputType ≤ fuel
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> Execution.executeField schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet leftInitialSpine rightInitialSpine
                targetParent leftField rightField leftArguments rightArguments
                leftRuntime rightRuntime)
              targetParent leftField rightField leftArguments rightArguments)
            variableValues (fuel + 1)
            (projectionTargetResolverValue
              (.object sourceRuntimeType
                (FieldPairSelectedPathProbeRef.target tag currentSelectionSet spine)))
            responseName
            [{
              parentType := parentType
              responseName := responseName
              fieldName := fieldName
              arguments := arguments
              selectionSet := childSelectionSet
            }]
          = .ok
              (
                [(
                  responseName,
                  leafProbeResponseValue fieldDefinition.outputType tag.scalar
                )],
                0
              ) := by
  intro hlookup hfuel hleaf
  let base :=
    fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
      rightInitialSelectionSet leftInitialSpine rightInitialSpine
      targetParent leftField rightField leftArguments rightArguments
      leftRuntime rightRuntime
  have hprojection :=
    executeField_fieldPairOrDeepSuccessResolvers_projectionTargetResolverValue
      schema rootSelectionSet base variableValues targetParent leftField
      rightField leftArguments rightArguments (fuel + 1)
      (.object sourceRuntimeType
        (FieldPairSelectedPathProbeRef.target tag currentSelectionSet
          spine))
      responseName
      [{
        parentType := parentType
        responseName := responseName
        fieldName := fieldName
        arguments := arguments
        selectionSet := childSelectionSet
      }]
  have hbase :=
    executeField_fieldPairSelectedPathProbe_tagged_object_leaf
      schema leftInitialSelectionSet rightInitialSelectionSet
      currentSelectionSet leftInitialSpine rightInitialSpine spine
      variableValues fuel targetParent leftField rightField parentType
      fieldName sourceRuntimeType responseName leftArguments
      rightArguments arguments leftRuntime rightRuntime tag
      childSelectionSet fieldDefinition hlookup hfuel hleaf
  simpa [base, hbase] using hprojection

theorem executeField_fieldPairSelectedPathProbe_tagged_object_objectOutput_response_of_fuel_ge
    (schema : Schema)
    (leftInitialSelectionSet rightInitialSelectionSet currentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine spine
      : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField parentType fieldName sourceRuntimeType responseName
      : Name)
    (leftArguments rightArguments arguments : List Argument)
    (leftRuntime rightRuntime : Name) (tag : FieldPairProbeTag)
    (childSelectionSet : List Selection) (fieldDefinition : FieldDefinition)
    : schema.lookupField parentType fieldName = some fieldDefinition
      -> objectTypeNameBool schema fieldDefinition.outputType.namedType = true
      -> leafProbeFuel fieldDefinition.outputType ≤ fuel
      -> Execution.executeField schema
            (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
              rightInitialSelectionSet leftInitialSpine rightInitialSpine
              targetParent leftField rightField leftArguments rightArguments
              leftRuntime rightRuntime)
            variableValues (fuel + 1)
            (.object sourceRuntimeType
              (FieldPairSelectedPathProbeRef.target tag currentSelectionSet spine))
            responseName
            [{
              parentType := parentType
              responseName := responseName
              fieldName := fieldName
              arguments := arguments
              selectionSet := childSelectionSet
            }]
          = Execution.singleFieldResult responseName
              (wrapTypeRefSelectionSetResult fieldDefinition.outputType
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
                    rightInitialSelectionSet leftInitialSpine rightInitialSpine
                    targetParent leftField rightField leftArguments rightArguments
                    leftRuntime rightRuntime)
                  variableValues
                  (fuel - leafProbeFuel fieldDefinition.outputType)
                  fieldDefinition.outputType.namedType
                  (.object fieldDefinition.outputType.namedType
                    (FieldPairSelectedPathProbeRef.target tag
                      (fieldPairPathLocalNextSelectionSet schema parentType
                        fieldDefinition.outputType.namedType fieldName arguments
                        currentSelectionSet)
                      (selectedObservableFieldSpineTailForRuntime
                        fieldDefinition.outputType.namedType fieldName arguments
                        spine)))
                  childSelectionSet)) := by
  intro hlookup hobject hfuel
  have hresolve :
      (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
          rightInitialSelectionSet leftInitialSpine rightInitialSpine
          targetParent leftField rightField leftArguments rightArguments
          leftRuntime rightRuntime).resolve
        parentType fieldName arguments
        (.object sourceRuntimeType
          (FieldPairSelectedPathProbeRef.target tag currentSelectionSet
            spine))
      =
      some
        (objectProbeResolverValueWithRuntime
          fieldDefinition.outputType.namedType
          (FieldPairSelectedPathProbeRef.target tag
            (fieldPairPathLocalNextSelectionSet schema parentType
              fieldDefinition.outputType.namedType fieldName arguments
              currentSelectionSet)
            (selectedObservableFieldSpineTailForRuntime
              fieldDefinition.outputType.namedType fieldName arguments
              spine))
          fieldDefinition.outputType) := by
    rw [fieldPairSelectedPathProbeResolvers_tagged_object schema
      leftInitialSelectionSet rightInitialSelectionSet currentSelectionSet
      leftInitialSpine rightInitialSpine spine targetParent leftField
      rightField parentType fieldName sourceRuntimeType leftArguments
      rightArguments arguments leftRuntime rightRuntime tag fieldDefinition
      hlookup]
    rw [
      fieldPairSelectedPathProbeHeadResolverValue_object_eq_objectProbeResolverValueWithRuntime
        schema currentSelectionSet parentType fieldName arguments tag spine
        fieldDefinition.outputType hobject]
  have hinclude :
      schema.typeIncludesObjectBool fieldDefinition.outputType.namedType
        fieldDefinition.outputType.namedType = true :=
    typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject
  exact
    executeField_objectProbeWithRuntime_response_of_fuel_ge schema
      (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
        rightInitialSelectionSet leftInitialSpine rightInitialSpine
        targetParent leftField rightField leftArguments rightArguments
        leftRuntime rightRuntime)
      variableValues fuel
      (.object sourceRuntimeType
        (FieldPairSelectedPathProbeRef.target tag currentSelectionSet
          spine))
      responseName parentType fieldName arguments childSelectionSet
      fieldDefinition fieldDefinition.outputType.namedType
      (FieldPairSelectedPathProbeRef.target tag
        (fieldPairPathLocalNextSelectionSet schema parentType
          fieldDefinition.outputType.namedType fieldName arguments
          currentSelectionSet)
        (selectedObservableFieldSpineTailForRuntime
          fieldDefinition.outputType.namedType fieldName arguments spine))
      hlookup hresolve hinclude hfuel

theorem executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_objectOutput_response_of_fuel_ge
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet currentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine spine
      : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField parentType fieldName sourceRuntimeType responseName
      : Name)
    (leftArguments rightArguments arguments : List Argument)
    (leftRuntime rightRuntime : Name) (tag : FieldPairProbeTag)
    (childSelectionSet : List Selection) (fieldDefinition : FieldDefinition)
    : schema.lookupField parentType fieldName = some fieldDefinition
      -> objectTypeNameBool schema fieldDefinition.outputType.namedType = true
      -> leafProbeFuel fieldDefinition.outputType ≤ fuel
      -> Execution.executeField schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet leftInitialSpine rightInitialSpine
                targetParent leftField rightField leftArguments rightArguments
                leftRuntime rightRuntime)
              targetParent leftField rightField leftArguments rightArguments)
            variableValues (fuel + 1)
            (projectionTargetResolverValue
              (.object sourceRuntimeType
                (FieldPairSelectedPathProbeRef.target tag currentSelectionSet spine)))
            responseName
            [{
              parentType := parentType
              responseName := responseName
              fieldName := fieldName
              arguments := arguments
              selectionSet := childSelectionSet
            }]
          = Execution.singleFieldResult responseName
              (wrapTypeRefSelectionSetResult fieldDefinition.outputType
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
                      rightInitialSelectionSet leftInitialSpine rightInitialSpine
                      targetParent leftField rightField leftArguments rightArguments
                      leftRuntime rightRuntime)
                    targetParent leftField rightField leftArguments rightArguments)
                  variableValues
                  (fuel - leafProbeFuel fieldDefinition.outputType)
                  fieldDefinition.outputType.namedType
                  (projectionTargetResolverValue
                    (.object fieldDefinition.outputType.namedType
                      (FieldPairSelectedPathProbeRef.target tag
                        (fieldPairPathLocalNextSelectionSet schema parentType
                          fieldDefinition.outputType.namedType fieldName arguments
                          currentSelectionSet)
                        (selectedObservableFieldSpineTailForRuntime
                          fieldDefinition.outputType.namedType fieldName arguments
                          spine))))
                  childSelectionSet)) := by
  intro hlookup hobject hfuel
  let base :=
    fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
      rightInitialSelectionSet leftInitialSpine rightInitialSpine
      targetParent leftField rightField leftArguments rightArguments
      leftRuntime rightRuntime
  have hprojection :=
    executeField_fieldPairOrDeepSuccessResolvers_projectionTargetResolverValue
      schema rootSelectionSet base variableValues targetParent leftField
      rightField leftArguments rightArguments (fuel + 1)
      (.object sourceRuntimeType
        (FieldPairSelectedPathProbeRef.target tag currentSelectionSet
          spine))
      responseName
      [{
        parentType := parentType
        responseName := responseName
        fieldName := fieldName
        arguments := arguments
        selectionSet := childSelectionSet
      }]
  have hbase :=
    executeField_fieldPairSelectedPathProbe_tagged_object_objectOutput_response_of_fuel_ge
      schema leftInitialSelectionSet rightInitialSelectionSet
      currentSelectionSet leftInitialSpine rightInitialSpine spine
      variableValues fuel targetParent leftField rightField parentType
      fieldName sourceRuntimeType responseName leftArguments
      rightArguments arguments leftRuntime rightRuntime tag
      childSelectionSet fieldDefinition hlookup hobject hfuel
  have hchildProjection :=
    executeSelectionSetAsResponse_fieldPairOrDeepSuccessResolvers_projectionTargetResolverValue
      schema rootSelectionSet base variableValues
      (fuel - leafProbeFuel fieldDefinition.outputType) targetParent
      leftField rightField leftArguments rightArguments
      fieldDefinition.outputType.namedType
      (.object fieldDefinition.outputType.namedType
        (FieldPairSelectedPathProbeRef.target tag
          (fieldPairPathLocalNextSelectionSet schema parentType
            fieldDefinition.outputType.namedType fieldName arguments
            currentSelectionSet)
          (selectedObservableFieldSpineTailForRuntime
            fieldDefinition.outputType.namedType fieldName arguments
            spine)))
      childSelectionSet
  simpa [base, hbase, hchildProjection] using hprojection

theorem executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_objectOutput_ok_of_child_response
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet currentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine spine
      : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField parentType fieldName sourceRuntimeType responseName
      : Name)
    (leftArguments rightArguments arguments : List Argument)
    (leftRuntime rightRuntime : Name) (tag : FieldPairProbeTag)
    (childSelectionSet : List Selection) (fieldDefinition : FieldDefinition)
    (responseFields : List (Name × Execution.ResponseValue)) (childErrors : Nat)
    : schema.lookupField parentType fieldName = some fieldDefinition
      -> objectTypeNameBool schema fieldDefinition.outputType.namedType = true
      -> leafProbeFuel fieldDefinition.outputType ≤ fuel
      -> Execution.executeSelectionSetAsResponse schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet leftInitialSpine rightInitialSpine
                targetParent leftField rightField leftArguments rightArguments
                leftRuntime rightRuntime)
              targetParent leftField rightField leftArguments rightArguments)
            variableValues
            (fuel - leafProbeFuel fieldDefinition.outputType)
            fieldDefinition.outputType.namedType
            (projectionTargetResolverValue
              (.object fieldDefinition.outputType.namedType
                (FieldPairSelectedPathProbeRef.target tag
                  (fieldPairPathLocalNextSelectionSet schema parentType
                    fieldDefinition.outputType.namedType fieldName arguments
                    currentSelectionSet)
                  (selectedObservableFieldSpineTailForRuntime
                    fieldDefinition.outputType.namedType fieldName arguments
                    spine))))
            childSelectionSet
          = ({
                data := Execution.ResponseValue.object responseFields,
                errors := childErrors
              }
              : Execution.Response)
      -> ∃ responseValue fieldErrors,
          Execution.executeField schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet leftInitialSpine rightInitialSpine
                  targetParent leftField rightField leftArguments rightArguments
                  leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1)
              (projectionTargetResolverValue
                (.object sourceRuntimeType
                  (FieldPairSelectedPathProbeRef.target tag currentSelectionSet spine)))
              responseName
              [{
                parentType := parentType
                responseName := responseName
                fieldName := fieldName
                arguments := arguments
                selectionSet := childSelectionSet
              }]
            = .ok ([(responseName, responseValue)], fieldErrors)
          ∧ responseValue ≠ Execution.ResponseValue.null := by
  intro hlookup hobject hfuel hchildResponse
  have hfield :=
    executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_objectOutput_response_of_fuel_ge
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet currentSelectionSet leftInitialSpine
      rightInitialSpine spine variableValues fuel targetParent
      leftField rightField parentType fieldName sourceRuntimeType
      responseName leftArguments rightArguments arguments leftRuntime
      rightRuntime tag childSelectionSet fieldDefinition hlookup
      hobject hfuel
  rcases
      wrapTypeRefSelectionSetResult_ok_nonNull_of_object_response
        fieldDefinition.outputType responseFields childErrors with
    ⟨responseValue, fieldErrors, hwrapped, hnonNull⟩
  refine ⟨responseValue, fieldErrors, ?_, hnonNull⟩
  rw [hfield, hchildResponse, hwrapped]
  simp [Execution.singleFieldResult]

theorem executeField_fieldPairSelectedPathProbe_tagged_object_abstractFallback_response_of_fuel_ge
    (schema : Schema)
    (leftInitialSelectionSet rightInitialSelectionSet currentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine spine
      : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField parentType fieldName sourceRuntimeType responseName
      : Name)
    (leftArguments rightArguments arguments : List Argument)
    (leftRuntime rightRuntime : Name) (tag : FieldPairProbeTag)
    (childSelectionSet : List Selection) (fieldDefinition : FieldDefinition)
    (runtimeType : Name)
    : schema.lookupField parentType fieldName = some fieldDefinition
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> objectTypeNameBool schema fieldDefinition.outputType.namedType = false
      -> selectedObservableFieldSpineNext? fieldName arguments spine = none
      -> abstractRuntimeForFieldHeadDeep? schema parentType fieldName arguments
            parentType currentSelectionSet
          = some runtimeType
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType runtimeType
          = true
      -> leafProbeFuel fieldDefinition.outputType ≤ fuel
      -> Execution.executeField schema
            (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
              rightInitialSelectionSet leftInitialSpine rightInitialSpine
              targetParent leftField rightField leftArguments rightArguments
              leftRuntime rightRuntime)
            variableValues (fuel + 1)
            (.object sourceRuntimeType
              (FieldPairSelectedPathProbeRef.target tag currentSelectionSet spine))
            responseName
            [{
              parentType := parentType
              responseName := responseName
              fieldName := fieldName
              arguments := arguments
              selectionSet := childSelectionSet
            }]
          = Execution.singleFieldResult responseName
              (wrapTypeRefSelectionSetResult fieldDefinition.outputType
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
                    rightInitialSelectionSet leftInitialSpine rightInitialSpine
                    targetParent leftField rightField leftArguments rightArguments
                    leftRuntime rightRuntime)
                  variableValues
                  (fuel - leafProbeFuel fieldDefinition.outputType)
                  runtimeType
                  (.object runtimeType
                    (FieldPairSelectedPathProbeRef.target tag
                      (fieldPairPathLocalNextSelectionSet schema parentType
                        runtimeType fieldName arguments currentSelectionSet)
                      []))
                  childSelectionSet)) := by
  intro hlookup hcomposite hnonObject hselectedNone hruntime hinclude
    hfuel
  have hresolve :
      (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
          rightInitialSelectionSet leftInitialSpine rightInitialSpine
          targetParent leftField rightField leftArguments rightArguments
          leftRuntime rightRuntime).resolve
        parentType fieldName arguments
        (.object sourceRuntimeType
          (FieldPairSelectedPathProbeRef.target tag currentSelectionSet
            spine))
      =
      some
        (objectProbeResolverValueWithRuntime runtimeType
          (FieldPairSelectedPathProbeRef.target tag
            (fieldPairPathLocalNextSelectionSet schema parentType
              runtimeType fieldName arguments currentSelectionSet)
            [])
          fieldDefinition.outputType) := by
    rw [fieldPairSelectedPathProbeResolvers_tagged_object schema
      leftInitialSelectionSet rightInitialSelectionSet currentSelectionSet
      leftInitialSpine rightInitialSpine spine targetParent leftField
      rightField parentType fieldName sourceRuntimeType leftArguments
      rightArguments arguments leftRuntime rightRuntime tag fieldDefinition
      hlookup]
    rw [
      fieldPairSelectedPathProbeHeadResolverValue_abstractFallback_eq_objectProbeResolverValueWithRuntime
        schema currentSelectionSet parentType fieldName runtimeType
        arguments tag spine fieldDefinition.outputType hcomposite
        hnonObject hselectedNone hruntime]
  exact
    executeField_objectProbeWithRuntime_response_of_fuel_ge schema
      (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
        rightInitialSelectionSet leftInitialSpine rightInitialSpine
        targetParent leftField rightField leftArguments rightArguments
        leftRuntime rightRuntime)
      variableValues fuel
      (.object sourceRuntimeType
        (FieldPairSelectedPathProbeRef.target tag currentSelectionSet
          spine))
      responseName parentType fieldName arguments childSelectionSet
      fieldDefinition runtimeType
      (FieldPairSelectedPathProbeRef.target tag
        (fieldPairPathLocalNextSelectionSet schema parentType runtimeType
          fieldName arguments currentSelectionSet)
        [])
      hlookup hresolve hinclude hfuel

theorem executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_abstractFallback_response_of_fuel_ge
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet currentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine spine
      : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField parentType fieldName sourceRuntimeType responseName
      : Name)
    (leftArguments rightArguments arguments : List Argument)
    (leftRuntime rightRuntime : Name) (tag : FieldPairProbeTag)
    (childSelectionSet : List Selection) (fieldDefinition : FieldDefinition)
    (runtimeType : Name)
    : schema.lookupField parentType fieldName = some fieldDefinition
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> objectTypeNameBool schema fieldDefinition.outputType.namedType = false
      -> selectedObservableFieldSpineNext? fieldName arguments spine = none
      -> abstractRuntimeForFieldHeadDeep? schema parentType fieldName arguments
            parentType currentSelectionSet
          = some runtimeType
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType runtimeType
          = true
      -> leafProbeFuel fieldDefinition.outputType ≤ fuel
      -> Execution.executeField schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet leftInitialSpine rightInitialSpine
                targetParent leftField rightField leftArguments rightArguments
                leftRuntime rightRuntime)
              targetParent leftField rightField leftArguments rightArguments)
            variableValues (fuel + 1)
            (projectionTargetResolverValue
              (.object sourceRuntimeType
                (FieldPairSelectedPathProbeRef.target tag currentSelectionSet spine)))
            responseName
            [{
              parentType := parentType
              responseName := responseName
              fieldName := fieldName
              arguments := arguments
              selectionSet := childSelectionSet
            }]
          = Execution.singleFieldResult responseName
              (wrapTypeRefSelectionSetResult fieldDefinition.outputType
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
                      rightInitialSelectionSet leftInitialSpine rightInitialSpine
                      targetParent leftField rightField leftArguments rightArguments
                      leftRuntime rightRuntime)
                    targetParent leftField rightField leftArguments rightArguments)
                  variableValues
                  (fuel - leafProbeFuel fieldDefinition.outputType)
                  runtimeType
                  (projectionTargetResolverValue
                    (.object runtimeType
                      (FieldPairSelectedPathProbeRef.target tag
                        (fieldPairPathLocalNextSelectionSet schema parentType
                          runtimeType fieldName arguments currentSelectionSet)
                        [])))
                  childSelectionSet)) := by
  intro hlookup hcomposite hnonObject hselectedNone hruntime hinclude
    hfuel
  let base :=
    fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
      rightInitialSelectionSet leftInitialSpine rightInitialSpine
      targetParent leftField rightField leftArguments rightArguments
      leftRuntime rightRuntime
  have hprojection :=
    executeField_fieldPairOrDeepSuccessResolvers_projectionTargetResolverValue
      schema rootSelectionSet base variableValues targetParent leftField
      rightField leftArguments rightArguments (fuel + 1)
      (.object sourceRuntimeType
        (FieldPairSelectedPathProbeRef.target tag currentSelectionSet
          spine))
      responseName
      [{
        parentType := parentType
        responseName := responseName
        fieldName := fieldName
        arguments := arguments
        selectionSet := childSelectionSet
      }]
  have hbase :=
    executeField_fieldPairSelectedPathProbe_tagged_object_abstractFallback_response_of_fuel_ge
      schema leftInitialSelectionSet rightInitialSelectionSet
      currentSelectionSet leftInitialSpine rightInitialSpine spine
      variableValues fuel targetParent leftField rightField parentType
      fieldName sourceRuntimeType responseName leftArguments
      rightArguments arguments leftRuntime rightRuntime tag
      childSelectionSet fieldDefinition runtimeType hlookup hcomposite
      hnonObject hselectedNone hruntime hinclude hfuel
  have hchildProjection :=
    executeSelectionSetAsResponse_fieldPairOrDeepSuccessResolvers_projectionTargetResolverValue
      schema rootSelectionSet base variableValues
      (fuel - leafProbeFuel fieldDefinition.outputType) targetParent
      leftField rightField leftArguments rightArguments runtimeType
      (.object runtimeType
        (FieldPairSelectedPathProbeRef.target tag
          (fieldPairPathLocalNextSelectionSet schema parentType runtimeType
            fieldName arguments currentSelectionSet)
          []))
      childSelectionSet
  simpa [base, hbase, hchildProjection] using hprojection

theorem executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_abstractFallback_ok_of_child_response
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet currentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine spine
      : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField parentType fieldName sourceRuntimeType responseName
      : Name)
    (leftArguments rightArguments arguments : List Argument)
    (leftRuntime rightRuntime : Name) (tag : FieldPairProbeTag)
    (childSelectionSet : List Selection) (fieldDefinition : FieldDefinition)
    (runtimeType : Name) (responseFields : List (Name × Execution.ResponseValue))
    (childErrors : Nat)
    : schema.lookupField parentType fieldName = some fieldDefinition
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> objectTypeNameBool schema fieldDefinition.outputType.namedType = false
      -> selectedObservableFieldSpineNext? fieldName arguments spine = none
      -> abstractRuntimeForFieldHeadDeep? schema parentType fieldName arguments
            parentType currentSelectionSet
          = some runtimeType
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType runtimeType
          = true
      -> leafProbeFuel fieldDefinition.outputType ≤ fuel
      -> Execution.executeSelectionSetAsResponse schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet leftInitialSpine rightInitialSpine
                targetParent leftField rightField leftArguments rightArguments
                leftRuntime rightRuntime)
              targetParent leftField rightField leftArguments rightArguments)
            variableValues
            (fuel - leafProbeFuel fieldDefinition.outputType)
            runtimeType
            (projectionTargetResolverValue
              (.object runtimeType
                (FieldPairSelectedPathProbeRef.target tag
                  (fieldPairPathLocalNextSelectionSet schema parentType
                    runtimeType fieldName arguments currentSelectionSet)
                  [])))
            childSelectionSet
          = ({
                data := Execution.ResponseValue.object responseFields,
                errors := childErrors
              }
              : Execution.Response)
      -> ∃ responseValue fieldErrors,
          Execution.executeField schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet leftInitialSpine rightInitialSpine
                  targetParent leftField rightField leftArguments rightArguments
                  leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1)
              (projectionTargetResolverValue
                (.object sourceRuntimeType
                  (FieldPairSelectedPathProbeRef.target tag currentSelectionSet spine)))
              responseName
              [{
                parentType := parentType
                responseName := responseName
                fieldName := fieldName
                arguments := arguments
                selectionSet := childSelectionSet
              }]
            = .ok ([(responseName, responseValue)], fieldErrors)
          ∧ responseValue ≠ Execution.ResponseValue.null := by
  intro hlookup hcomposite hnonObject hselectedNone hruntime hinclude
    hfuel hchildResponse
  have hfield :=
    executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_abstractFallback_response_of_fuel_ge
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet currentSelectionSet leftInitialSpine
      rightInitialSpine spine variableValues fuel targetParent
      leftField rightField parentType fieldName sourceRuntimeType
      responseName leftArguments rightArguments arguments leftRuntime
      rightRuntime tag childSelectionSet fieldDefinition runtimeType
      hlookup hcomposite hnonObject hselectedNone hruntime hinclude
      hfuel
  rcases
      wrapTypeRefSelectionSetResult_ok_nonNull_of_object_response
        fieldDefinition.outputType responseFields childErrors with
    ⟨responseValue, fieldErrors, hwrapped, hnonNull⟩
  refine ⟨responseValue, fieldErrors, ?_, hnonNull⟩
  rw [hfield, hchildResponse, hwrapped]
  simp [Execution.singleFieldResult]

theorem executeField_fieldPairSelectedPathProbe_tagged_object_objectProbe_response_of_fuel_ge
    (schema : Schema)
    (leftInitialSelectionSet rightInitialSelectionSet currentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine spine tail
      : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField parentType fieldName sourceRuntimeType responseName
      : Name)
    (leftArguments rightArguments arguments : List Argument)
    (leftRuntime rightRuntime : Name) (tag : FieldPairProbeTag)
    (childSelectionSet : List Selection) (fieldDefinition : FieldDefinition)
    (runtimeType : Name)
    : schema.lookupField parentType fieldName = some fieldDefinition
      -> selectedObservableFieldSpineNext? fieldName arguments spine
          = some (some runtimeType, tail)
      -> ((objectTypeNameBool schema fieldDefinition.outputType.namedType = true
            ∧ runtimeType = fieldDefinition.outputType.namedType)
          ∨ ((TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
                = true
              ∧ objectTypeNameBool schema fieldDefinition.outputType.namedType = false))
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType runtimeType
          = true
      -> leafProbeFuel fieldDefinition.outputType ≤ fuel
      -> Execution.executeField schema
            (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
              rightInitialSelectionSet leftInitialSpine rightInitialSpine
              targetParent leftField rightField leftArguments rightArguments
              leftRuntime rightRuntime)
            variableValues (fuel + 1)
            (.object sourceRuntimeType
              (FieldPairSelectedPathProbeRef.target tag currentSelectionSet spine))
            responseName
            [{
              parentType := parentType
              responseName := responseName
              fieldName := fieldName
              arguments := arguments
              selectionSet := childSelectionSet
            }]
          = Execution.singleFieldResult responseName
              (wrapTypeRefSelectionSetResult fieldDefinition.outputType
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
                    rightInitialSelectionSet leftInitialSpine rightInitialSpine
                    targetParent leftField rightField leftArguments rightArguments
                    leftRuntime rightRuntime)
                  variableValues
                  (fuel - leafProbeFuel fieldDefinition.outputType)
                  runtimeType
                  (.object runtimeType
                    (FieldPairSelectedPathProbeRef.target tag
                      (fieldPairPathLocalNextSelectionSet schema parentType
                        runtimeType fieldName arguments currentSelectionSet)
                      tail))
                  childSelectionSet)) := by
  intro hlookup hselected hcase hinclude hfuel
  have hresolve :
      (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
          rightInitialSelectionSet leftInitialSpine rightInitialSpine
          targetParent leftField rightField leftArguments rightArguments
          leftRuntime rightRuntime).resolve
        parentType fieldName arguments
        (.object sourceRuntimeType
          (FieldPairSelectedPathProbeRef.target tag currentSelectionSet
            spine))
      =
      some
        (objectProbeResolverValueWithRuntime runtimeType
          (FieldPairSelectedPathProbeRef.target tag
            (fieldPairPathLocalNextSelectionSet schema parentType
              runtimeType fieldName arguments currentSelectionSet)
            tail)
          fieldDefinition.outputType) := by
    exact
      fieldPairSelectedPathProbeResolvers_tagged_object_selected_runtime
        schema leftInitialSelectionSet rightInitialSelectionSet
        currentSelectionSet leftInitialSpine rightInitialSpine spine tail
        targetParent leftField rightField parentType fieldName
        sourceRuntimeType runtimeType leftArguments rightArguments
        arguments leftRuntime rightRuntime tag fieldDefinition hlookup
        hselected hcase
  exact
    executeField_objectProbeWithRuntime_response_of_fuel_ge schema
      (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
        rightInitialSelectionSet leftInitialSpine rightInitialSpine
        targetParent leftField rightField leftArguments rightArguments
        leftRuntime rightRuntime)
      variableValues fuel
      (.object sourceRuntimeType
        (FieldPairSelectedPathProbeRef.target tag currentSelectionSet
          spine))
      responseName parentType fieldName arguments childSelectionSet
      fieldDefinition runtimeType
      (FieldPairSelectedPathProbeRef.target tag
        (fieldPairPathLocalNextSelectionSet schema parentType runtimeType
          fieldName arguments currentSelectionSet)
        tail)
      hlookup hresolve hinclude hfuel

theorem executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_objectProbe_response_of_fuel_ge
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet currentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine spine tail
      : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField parentType fieldName sourceRuntimeType responseName
      : Name)
    (leftArguments rightArguments arguments : List Argument)
    (leftRuntime rightRuntime : Name) (tag : FieldPairProbeTag)
    (childSelectionSet : List Selection) (fieldDefinition : FieldDefinition)
    (runtimeType : Name)
    : schema.lookupField parentType fieldName = some fieldDefinition
      -> selectedObservableFieldSpineNext? fieldName arguments spine
          = some (some runtimeType, tail)
      -> ((objectTypeNameBool schema fieldDefinition.outputType.namedType = true
            ∧ runtimeType = fieldDefinition.outputType.namedType)
          ∨ ((TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
                = true
              ∧ objectTypeNameBool schema fieldDefinition.outputType.namedType = false))
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType runtimeType
          = true
      -> leafProbeFuel fieldDefinition.outputType ≤ fuel
      -> Execution.executeField schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet leftInitialSpine rightInitialSpine
                targetParent leftField rightField leftArguments rightArguments
                leftRuntime rightRuntime)
              targetParent leftField rightField leftArguments rightArguments)
            variableValues (fuel + 1)
            (projectionTargetResolverValue
              (.object sourceRuntimeType
                (FieldPairSelectedPathProbeRef.target tag currentSelectionSet spine)))
            responseName
            [{
              parentType := parentType
              responseName := responseName
              fieldName := fieldName
              arguments := arguments
              selectionSet := childSelectionSet
            }]
          = Execution.singleFieldResult responseName
              (wrapTypeRefSelectionSetResult fieldDefinition.outputType
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
                      rightInitialSelectionSet leftInitialSpine rightInitialSpine
                      targetParent leftField rightField leftArguments rightArguments
                      leftRuntime rightRuntime)
                    targetParent leftField rightField leftArguments rightArguments)
                  variableValues
                  (fuel - leafProbeFuel fieldDefinition.outputType)
                  runtimeType
                  (projectionTargetResolverValue
                    (.object runtimeType
                      (FieldPairSelectedPathProbeRef.target tag
                        (fieldPairPathLocalNextSelectionSet schema parentType
                          runtimeType fieldName arguments currentSelectionSet)
                        tail)))
                  childSelectionSet)) := by
  intro hlookup hselected hcase hinclude hfuel
  let base :=
    fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
      rightInitialSelectionSet leftInitialSpine rightInitialSpine
      targetParent leftField rightField leftArguments rightArguments
      leftRuntime rightRuntime
  have hprojection :=
    executeField_fieldPairOrDeepSuccessResolvers_projectionTargetResolverValue
      schema rootSelectionSet base variableValues targetParent leftField
      rightField leftArguments rightArguments (fuel + 1)
      (.object sourceRuntimeType
        (FieldPairSelectedPathProbeRef.target tag currentSelectionSet
          spine))
      responseName
      [{
        parentType := parentType
        responseName := responseName
        fieldName := fieldName
        arguments := arguments
        selectionSet := childSelectionSet
      }]
  have hbase :=
    executeField_fieldPairSelectedPathProbe_tagged_object_objectProbe_response_of_fuel_ge
      schema leftInitialSelectionSet rightInitialSelectionSet
      currentSelectionSet leftInitialSpine rightInitialSpine spine tail
      variableValues fuel targetParent leftField rightField parentType
      fieldName sourceRuntimeType responseName leftArguments
      rightArguments arguments leftRuntime rightRuntime tag
      childSelectionSet fieldDefinition runtimeType hlookup hselected
      hcase hinclude hfuel
  have hchildProjection :=
    executeSelectionSetAsResponse_fieldPairOrDeepSuccessResolvers_projectionTargetResolverValue
      schema rootSelectionSet base variableValues
      (fuel - leafProbeFuel fieldDefinition.outputType) targetParent
      leftField rightField leftArguments rightArguments runtimeType
      (.object runtimeType
        (FieldPairSelectedPathProbeRef.target tag
          (fieldPairPathLocalNextSelectionSet schema parentType runtimeType
            fieldName arguments currentSelectionSet)
          tail))
      childSelectionSet
  simpa [base, hbase, hchildProjection] using hprojection

theorem executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_objectProbe_ok_of_child_response
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet currentSelectionSet
      : List Selection)
    (leftInitialSpine rightInitialSpine spine tail
      : List NormalSelectionSetObservableFieldStep)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField parentType fieldName sourceRuntimeType responseName
      : Name)
    (leftArguments rightArguments arguments : List Argument)
    (leftRuntime rightRuntime : Name) (tag : FieldPairProbeTag)
    (childSelectionSet : List Selection) (fieldDefinition : FieldDefinition)
    (runtimeType : Name) (responseFields : List (Name × Execution.ResponseValue))
    (childErrors : Nat)
    : schema.lookupField parentType fieldName = some fieldDefinition
      -> selectedObservableFieldSpineNext? fieldName arguments spine
          = some (some runtimeType, tail)
      -> ((objectTypeNameBool schema fieldDefinition.outputType.namedType = true
            ∧ runtimeType = fieldDefinition.outputType.namedType)
          ∨ ((TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
                = true
              ∧ objectTypeNameBool schema fieldDefinition.outputType.namedType = false))
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType runtimeType
          = true
      -> leafProbeFuel fieldDefinition.outputType ≤ fuel
      -> Execution.executeSelectionSetAsResponse schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet leftInitialSpine rightInitialSpine
                targetParent leftField rightField leftArguments rightArguments
                leftRuntime rightRuntime)
              targetParent leftField rightField leftArguments rightArguments)
            variableValues
            (fuel - leafProbeFuel fieldDefinition.outputType)
            runtimeType
            (projectionTargetResolverValue
              (.object runtimeType
                (FieldPairSelectedPathProbeRef.target tag
                  (fieldPairPathLocalNextSelectionSet schema parentType
                    runtimeType fieldName arguments currentSelectionSet)
                  tail)))
            childSelectionSet
          = ({
                data := Execution.ResponseValue.object responseFields,
                errors := childErrors
              }
              : Execution.Response)
      -> ∃ responseValue fieldErrors,
          Execution.executeField schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSelectedPathProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet leftInitialSpine rightInitialSpine
                  targetParent leftField rightField leftArguments rightArguments
                  leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1)
              (projectionTargetResolverValue
                (.object sourceRuntimeType
                  (FieldPairSelectedPathProbeRef.target tag currentSelectionSet spine)))
              responseName
              [{
                parentType := parentType
                responseName := responseName
                fieldName := fieldName
                arguments := arguments
                selectionSet := childSelectionSet
              }]
            = .ok ([(responseName, responseValue)], fieldErrors)
          ∧ responseValue ≠ Execution.ResponseValue.null := by
  intro hlookup hselected hcase hinclude hfuel hchildResponse
  have hfield :=
    executeField_fieldPairOrDeepSuccess_selectedPathProbe_tagged_object_objectProbe_response_of_fuel_ge
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet currentSelectionSet leftInitialSpine
      rightInitialSpine spine tail variableValues fuel targetParent
      leftField rightField parentType fieldName sourceRuntimeType
      responseName leftArguments rightArguments arguments leftRuntime
      rightRuntime tag childSelectionSet fieldDefinition runtimeType
      hlookup hselected hcase hinclude hfuel
  rcases
      wrapTypeRefSelectionSetResult_ok_nonNull_of_object_response
        fieldDefinition.outputType responseFields childErrors with
    ⟨responseValue, fieldErrors, hwrapped, hnonNull⟩
  refine ⟨responseValue, fieldErrors, ?_, hnonNull⟩
  rw [hfield, hchildResponse, hwrapped]
  simp [Execution.singleFieldResult]

end GroundTypeNormalization

end NormalForm

end GraphQL
