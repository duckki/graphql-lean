import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.FocusedTrace
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.RuntimeCoherence

/-!
Focused runtime-coherence support.

The older `SelectionSetProbeRootCoherentDeep` invariant describes every field in
a selection set.  That is stronger than the uniqueness proof needs: semantic
separation follows one response path selected by `NormalSelectionSetDiffTrace`.
This module records only that path-local coherence.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

theorem runtimePrunedSelectionSet_append
    (schema : Schema) (runtimeType : Name)
    (left right : List Selection)
    : runtimePrunedSelectionSet schema runtimeType (left ++ right)
      = runtimePrunedSelectionSet schema runtimeType left
        ++ runtimePrunedSelectionSet schema runtimeType right := by
  induction left with
  | nil =>
      simp [runtimePrunedSelectionSet]
  | cons selection rest ih =>
      cases selection with
      | field responseName fieldName arguments directives childSelectionSet =>
          simp [runtimePrunedSelectionSet, ih]
      | inlineFragment typeCondition directives childSelectionSet =>
          cases typeCondition with
          | none =>
              simp [runtimePrunedSelectionSet, ih, List.append_assoc]
          | some typeCondition =>
              by_cases hincludes :
                  schema.typeIncludesObjectBool typeCondition runtimeType
              · simp [runtimePrunedSelectionSet, hincludes, ih,
                  List.append_assoc]
              · simp [runtimePrunedSelectionSet, hincludes, ih]

inductive SelectionSetProbePathCoherent
    (schema : Schema) (rootSelectionSet : List Selection)
    : Name -> List Selection -> List Name -> Prop where
  | objectHere
    {parentType responseName fieldName : Name}
    {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    : objectTypeNameBool schema parentType = true
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> SelectionSetProbePathCoherent schema rootSelectionSet parentType
          selectionSet [responseName]
  | objectChild
    {parentType responseName fieldName : Name}
    {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    {childPath : List Name}
    : objectTypeNameBool schema parentType = true
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> (∀ _hcomposite : (TypeRef.named
                            fieldDefinition.outputType.namedType).isCompositeBool
                            schema
                          = true,
            ∃ runtimeType,
              fieldHeadProbeRuntimeCoherent schema rootSelectionSet parentType
                fieldName runtimeType arguments fieldDefinition
                childSelectionSet)
      -> SelectionSetProbePathCoherent schema rootSelectionSet
          fieldDefinition.outputType.namedType childSelectionSet childPath
      -> SelectionSetProbePathCoherent schema rootSelectionSet parentType
          selectionSet (responseName :: childPath)
  | abstractInlineFragment
    {parentType typeCondition : Name}
    {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    {childPath : List Name}
    : objectTypeNameBool schema parentType = false
      -> Selection.inlineFragment (some typeCondition) directives childSelectionSet
          ∈ selectionSet
      -> SelectionSetProbePathCoherent schema rootSelectionSet typeCondition
          childSelectionSet childPath
      -> SelectionSetProbePathCoherent schema rootSelectionSet parentType
          selectionSet childPath

theorem SelectionSetProbePathCoherent.selectionSet_nonempty
    {schema : Schema} {rootSelectionSet selectionSet : List Selection}
    {parentType : Name} {responsePath : List Name}
    : SelectionSetProbePathCoherent schema rootSelectionSet parentType
        selectionSet responsePath
      -> selectionSet ≠ [] := by
  intro hpath hempty
  cases hpath with
  | objectHere _hobject hmem =>
      subst selectionSet
      simp at hmem
  | objectChild _hobject hmem _hlookup _hhead _hchildPath =>
      subst selectionSet
      simp at hmem
  | abstractInlineFragment _hnonObject hmem _hchildPath =>
      subst selectionSet
      simp at hmem

theorem SelectionSetProbeRootCoherentDeep.pathCoherent_of_responsePath
    {schema : Schema} {rootSelectionSet selectionSet : List Selection}
    {parentType : Name} {responsePath : List Name}
    : SelectionSetProbeRootCoherentDeep schema rootSelectionSet parentType selectionSet
      -> NormalSelectionSetResponsePath schema parentType selectionSet responsePath
      -> SelectionSetProbePathCoherent schema rootSelectionSet parentType
          selectionSet responsePath := by
  intro hcoherent hpath
  induction hpath with
  | objectHere hobject hmem =>
      exact SelectionSetProbePathCoherent.objectHere hobject hmem
  | objectChild hobject hmem hlookup _hchildPath ih =>
      have hchildCoherent :=
        hcoherent.field_child_of_mem hmem hlookup
      exact
        SelectionSetProbePathCoherent.objectChild hobject hmem hlookup
          (fun hcomposite =>
            hcoherent.field_head_of_mem hmem hlookup hcomposite)
          (ih hchildCoherent)
  | abstractInlineFragment hnonObject hmem _hchildPath ih =>
      have hchildCoherent :=
        hcoherent.inlineFragment_some_child_of_mem hmem
      exact
        SelectionSetProbePathCoherent.abstractInlineFragment hnonObject hmem
          (ih hchildCoherent)

theorem NormalSelectionSetResponsePath.runtimeActive_of_normal
    {schema : Schema} {selectionSet : List Selection}
    {variableDefinitions : List VariableDefinition}
    {parentType : Name} {responsePath : List Name}
    : Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> NormalSelectionSetResponsePath schema parentType selectionSet responsePath
      -> ∃ runtimeType,
          selectionSetRuntimeActive schema parentType runtimeType selectionSet
          ∧ schema.typeIncludesObjectBool parentType runtimeType = true := by
  intro hvalid hnormal hpath
  cases hpath with
  | objectHere hobject _hmem =>
      exact ⟨
        parentType,
        selectionSetRuntimeActive_object hobject,
        typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject
      ⟩
  | objectChild hobject _hmem _hlookup _hchildPath =>
      exact ⟨
        parentType,
        selectionSetRuntimeActive_object hobject,
        typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject
      ⟩
  | abstractInlineFragment hnonObject hmem hchildPath =>
      rcases selectionSetNormal_inlineFragment_child_of_mem hnormal hmem with
        ⟨htypeObject, hchildNormal⟩
      have hoverlap : schema.typesOverlap parentType _ :=
        selectionSetValid_inlineFragment_some_typesOverlap_of_mem hvalid hmem
      have hinclude : schema.typeIncludesObjectBool parentType _ = true :=
        typeIncludesObjectBool_of_typesOverlap_object schema hoverlap
          htypeObject
      exact ⟨
        _,
        Or.inr
          ⟨
            hnonObject,
            _,
            _,
            hmem,
            normalSelectionSetResponsePath_selectionSet_nonempty hchildPath,
            hchildNormal
          ⟩,
        hinclude
      ⟩

theorem NormalSelectionSetResponsePath.runtimePruned_of_normal
    {schema : Schema} {selectionSet : List Selection}
    {variableDefinitions : List VariableDefinition}
    {parentType : Name} {responsePath : List Name}
    : Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> NormalSelectionSetResponsePath schema parentType selectionSet responsePath
      -> ∃ runtimeType,
          selectionSetRuntimeActive schema parentType runtimeType selectionSet
          ∧ schema.typeIncludesObjectBool parentType runtimeType = true
          ∧ NormalSelectionSetResponsePath schema runtimeType
              (runtimePrunedSelectionSet schema runtimeType selectionSet)
              responsePath := by
  intro hvalid hnormal hpath
  induction hpath with
  | objectHere hobject hmem =>
      rename_i pathParentType responseName fieldName arguments directives
        childSelectionSet pathSelectionSet
      have hnormalLocal := by
        simpa using hnormal
      have hallFields :
          selectionsAllFields pathSelectionSet :=
        selectionSetNormal_allFields_of_object hnormalLocal hobject
      have hpruned :
          runtimePrunedSelectionSet schema pathParentType pathSelectionSet =
            pathSelectionSet :=
        runtimePrunedSelectionSet_eq_self_of_allFields schema pathParentType
          hallFields
      exact ⟨
        pathParentType,
        selectionSetRuntimeActive_object hobject,
        typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject,
        by
          rw [hpruned]
          exact NormalSelectionSetResponsePath.objectHere hobject hmem
      ⟩
  | objectChild hobject hmem hlookup hchildPath ih =>
      rename_i pathParentType responseName fieldName arguments directives
        childSelectionSet pathSelectionSet fieldDefinition childPath
      have hnormalLocal := by
        simpa using hnormal
      have hallFields :
          selectionsAllFields pathSelectionSet :=
        selectionSetNormal_allFields_of_object hnormalLocal hobject
      have hpruned :
          runtimePrunedSelectionSet schema pathParentType pathSelectionSet =
            pathSelectionSet :=
        runtimePrunedSelectionSet_eq_self_of_allFields schema pathParentType
          hallFields
      exact ⟨
        pathParentType,
        selectionSetRuntimeActive_object hobject,
        typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject,
        by
          rw [hpruned]
          exact
            NormalSelectionSetResponsePath.objectChild hobject hmem hlookup
              hchildPath
      ⟩
  | abstractInlineFragment hnonObject hmem hchildPath ih =>
      rename_i pathParentType typeCondition directives childSelectionSet
        pathSelectionSet childPath
      have hnormalLocal := by
        simpa using hnormal
      have hvalidLocal := by
        simpa using hvalid
      have hchildValid :
          Validation.selectionSetValid schema variableDefinitions
            typeCondition childSelectionSet :=
        selectionSetValid_inlineFragment_some_child_of_mem hvalidLocal hmem
      rcases selectionSetNormal_inlineFragment_child_of_mem hnormalLocal hmem with
        ⟨htypeObject, hchildNormal⟩
      have hoverlap : schema.typesOverlap pathParentType typeCondition :=
        selectionSetValid_inlineFragment_some_typesOverlap_of_mem hvalidLocal
          hmem
      have hinclude :
          schema.typeIncludesObjectBool pathParentType typeCondition =
            true :=
        typeIncludesObjectBool_of_typesOverlap_object schema hoverlap
          htypeObject
      rcases ih hchildValid hchildNormal with
        ⟨childRuntimeType, _hchildActive, hchildInclude,
          hchildPrunedPath⟩
      have hchildRuntimeEq : childRuntimeType = typeCondition :=
        typeIncludesObjectBool_eq_of_objectTypeNameBool_true schema
          (objectTypeNameBool_eq_true_of_objectType_base schema htypeObject)
          hchildInclude
      subst childRuntimeType
      have hincludeSelf :
          schema.typeIncludesObjectBool _ _ = true :=
        typeIncludesObjectBool_self_of_objectTypeNameBool schema
          (objectTypeNameBool_eq_true_of_objectType_base schema htypeObject)
      rcases List.mem_iff_append.mp hmem with ⟨pref, suff, hselectionSet⟩
      refine ⟨
        _,
        Or.inr
          ⟨
            hnonObject,
            directives,
            childSelectionSet,
            ?_,
            normalSelectionSetResponsePath_selectionSet_nonempty hchildPath,
            hchildNormal
          ⟩,
        hinclude,
        ?_
      ⟩
      · exact hmem
      · rw [hselectionSet]
        simp [runtimePrunedSelectionSet_append, runtimePrunedSelectionSet,
          hincludeSelf]
        simpa [List.append_assoc] using
          (NormalSelectionSetResponsePath.append_context
            (pref := runtimePrunedSelectionSet schema typeCondition pref)
            (suff := runtimePrunedSelectionSet schema typeCondition suff)
            hchildPrunedPath)

theorem NormalSelectionSetObservableResponsePath.runtimePruned_of_normal
    {schema : Schema} {selectionSet : List Selection}
    {variableDefinitions : List VariableDefinition}
    {parentType : Name} {responsePath : List Name}
    : Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> NormalSelectionSetObservableResponsePath schema parentType selectionSet
          responsePath
      -> ∃ runtimeType,
          selectionSetRuntimeActive schema parentType runtimeType selectionSet
          ∧ schema.typeIncludesObjectBool parentType runtimeType = true
          ∧ NormalSelectionSetObservableResponsePath schema runtimeType
              (runtimePrunedSelectionSet schema runtimeType selectionSet)
              responsePath := by
  intro hvalid hnormal hpath
  induction hpath with
  | objectLeaf hobject hmem hlookup hleaf =>
      rename_i pathParentType responseName fieldName arguments directives
        childSelectionSet pathSelectionSet fieldDefinition
      have hnormalLocal := by
        simpa using hnormal
      have hallFields :
          selectionsAllFields pathSelectionSet :=
        selectionSetNormal_allFields_of_object hnormalLocal hobject
      have hpruned :
          runtimePrunedSelectionSet schema pathParentType pathSelectionSet =
            pathSelectionSet :=
        runtimePrunedSelectionSet_eq_self_of_allFields schema pathParentType
          hallFields
      exact ⟨
        pathParentType,
        selectionSetRuntimeActive_object hobject,
        typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject,
        by
          rw [hpruned]
          exact
            NormalSelectionSetObservableResponsePath.objectLeaf hobject
              hmem hlookup hleaf
      ⟩
  | objectChild hobject hmem hlookup hcomposite hchildPath ih =>
      rename_i pathParentType responseName fieldName arguments directives
        childSelectionSet pathSelectionSet fieldDefinition childPath
      have hnormalLocal := by
        simpa using hnormal
      have hallFields :
          selectionsAllFields pathSelectionSet :=
        selectionSetNormal_allFields_of_object hnormalLocal hobject
      have hpruned :
          runtimePrunedSelectionSet schema pathParentType pathSelectionSet =
            pathSelectionSet :=
        runtimePrunedSelectionSet_eq_self_of_allFields schema pathParentType
          hallFields
      exact ⟨
        pathParentType,
        selectionSetRuntimeActive_object hobject,
        typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject,
        by
          rw [hpruned]
          exact
            NormalSelectionSetObservableResponsePath.objectChild hobject
              hmem hlookup hcomposite hchildPath
      ⟩
  | abstractInlineFragment hnonObject hmem hchildPath ih =>
      rename_i pathParentType typeCondition directives childSelectionSet
        pathSelectionSet childPath
      have hnormalLocal := by
        simpa using hnormal
      have hvalidLocal := by
        simpa using hvalid
      have hchildValid :
          Validation.selectionSetValid schema variableDefinitions
            typeCondition childSelectionSet :=
        selectionSetValid_inlineFragment_some_child_of_mem hvalidLocal hmem
      rcases selectionSetNormal_inlineFragment_child_of_mem hnormalLocal hmem with
        ⟨htypeObject, hchildNormal⟩
      have hoverlap : schema.typesOverlap pathParentType typeCondition :=
        selectionSetValid_inlineFragment_some_typesOverlap_of_mem hvalidLocal
          hmem
      have hinclude :
          schema.typeIncludesObjectBool pathParentType typeCondition =
            true :=
        typeIncludesObjectBool_of_typesOverlap_object schema hoverlap
          htypeObject
      rcases ih hchildValid hchildNormal with
        ⟨childRuntimeType, _hchildActive, hchildInclude,
          hchildPrunedPath⟩
      have hchildRuntimeEq : childRuntimeType = typeCondition :=
        typeIncludesObjectBool_eq_of_objectTypeNameBool_true schema
          (objectTypeNameBool_eq_true_of_objectType_base schema htypeObject)
          hchildInclude
      subst childRuntimeType
      have hincludeSelf :
          schema.typeIncludesObjectBool _ _ = true :=
        typeIncludesObjectBool_self_of_objectTypeNameBool schema
          (objectTypeNameBool_eq_true_of_objectType_base schema htypeObject)
      rcases List.mem_iff_append.mp hmem with ⟨pref, suff, hselectionSet⟩
      refine ⟨
        _,
        Or.inr
          ⟨
            hnonObject,
            directives,
            childSelectionSet,
            ?_,
            normalSelectionSetResponsePath_selectionSet_nonempty
              hchildPath.to_responsePath,
            hchildNormal
          ⟩,
        hinclude,
        ?_
      ⟩
      · exact hmem
      · rw [hselectionSet]
        simp [runtimePrunedSelectionSet_append, runtimePrunedSelectionSet,
          hincludeSelf]
        simpa [List.append_assoc] using
          (NormalSelectionSetObservableResponsePath.append_context
            (pref := runtimePrunedSelectionSet schema typeCondition pref)
            (suff := runtimePrunedSelectionSet schema typeCondition suff)
            hchildPrunedPath)

theorem SelectionSetProbePathCoherent.runtimeActive_of_normal
    {schema : Schema} {rootSelectionSet selectionSet : List Selection}
    {variableDefinitions : List VariableDefinition}
    {parentType : Name} {responsePath : List Name}
    : Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> SelectionSetProbePathCoherent schema rootSelectionSet parentType
          selectionSet responsePath
      -> ∃ runtimeType,
          selectionSetRuntimeActive schema parentType runtimeType selectionSet
          ∧ schema.typeIncludesObjectBool parentType runtimeType = true := by
  intro hvalid hnormal hpath
  cases hpath with
  | objectHere hobject _hmem =>
      exact ⟨
        parentType,
        selectionSetRuntimeActive_object hobject,
        typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject
      ⟩
  | objectChild hobject _hmem _hlookup _hhead _hchildPath =>
      exact ⟨
        parentType,
        selectionSetRuntimeActive_object hobject,
        typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject
      ⟩
  | abstractInlineFragment hnonObject hmem hchildPath =>
      rcases selectionSetNormal_inlineFragment_child_of_mem hnormal hmem with
        ⟨htypeObject, hchildNormal⟩
      have hoverlap : schema.typesOverlap parentType _ :=
        selectionSetValid_inlineFragment_some_typesOverlap_of_mem hvalid hmem
      have hinclude : schema.typeIncludesObjectBool parentType _ = true :=
        typeIncludesObjectBool_of_typesOverlap_object schema hoverlap
          htypeObject
      exact ⟨
        _,
        Or.inr ⟨hnonObject, _, _, hmem, hchildPath.selectionSet_nonempty, hchildNormal⟩,
        hinclude
      ⟩

theorem fieldHeadProbeRuntimeCoherent_of_child_pathCoherent
    {schema : Schema} {rootSelectionSet childSelectionSet : List Selection}
    {parentType fieldName : Name} {arguments : List Argument}
    {variableDefinitions : List VariableDefinition}
    {fieldDefinition : FieldDefinition} {childPath : List Name}
    : Validation.selectionSetValid schema variableDefinitions
        fieldDefinition.outputType.namedType childSelectionSet
      -> selectionSetNormal schema fieldDefinition.outputType.namedType childSelectionSet
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> SelectionSetProbePathCoherent schema rootSelectionSet
          fieldDefinition.outputType.namedType childSelectionSet childPath
      -> (∀ runtimeType,
            selectionSetRuntimeActive schema fieldDefinition.outputType.namedType
              runtimeType childSelectionSet
            -> objectTypeNameBool schema fieldDefinition.outputType.namedType = false
            -> abstractRuntimeForFieldHeadDeep? schema parentType fieldName
                  arguments parentType rootSelectionSet
                = some runtimeType)
      -> ∃ runtimeType,
          fieldHeadProbeRuntimeCoherent schema rootSelectionSet parentType
            fieldName runtimeType arguments fieldDefinition childSelectionSet := by
  intro hchildValid hchildNormal hcomposite hchildPath hrootPreservesRuntime
  by_cases hobject :
      objectTypeNameBool schema fieldDefinition.outputType.namedType = true
  · exact ⟨fieldDefinition.outputType.namedType, Or.inl ⟨hobject, rfl⟩⟩
  · have hnonObject :
        objectTypeNameBool schema fieldDefinition.outputType.namedType =
          false := by
      cases h :
          objectTypeNameBool schema fieldDefinition.outputType.namedType
      · rfl
      · exact False.elim (hobject h)
    rcases
        hchildPath.runtimeActive_of_normal hchildValid hchildNormal with
      ⟨runtimeType, hactive, _hinclude⟩
    exact ⟨
      runtimeType,
      Or.inr
        ⟨
          hcomposite,
          hnonObject,
          hrootPreservesRuntime runtimeType hactive hnonObject,
          hactive
        ⟩
    ⟩

theorem SelectionSetProbePathCoherent.objectChild_of_runtimePreserving
    {schema : Schema} {rootSelectionSet selectionSet childSelectionSet : List Selection}
    {parentType responseName fieldName : Name}
    {arguments : List Argument}
    {directives : List DirectiveApplication}
    {variableDefinitions : List VariableDefinition}
    {fieldDefinition : FieldDefinition} {childPath : List Name}
    : objectTypeNameBool schema parentType = true
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> Validation.selectionSetValid schema variableDefinitions
          fieldDefinition.outputType.namedType childSelectionSet
      -> selectionSetNormal schema fieldDefinition.outputType.namedType childSelectionSet
      -> SelectionSetProbePathCoherent schema rootSelectionSet
          fieldDefinition.outputType.namedType childSelectionSet childPath
      -> (∀ runtimeType,
            selectionSetRuntimeActive schema fieldDefinition.outputType.namedType
              runtimeType childSelectionSet
            -> objectTypeNameBool schema fieldDefinition.outputType.namedType = false
            -> abstractRuntimeForFieldHeadDeep? schema parentType fieldName
                  arguments parentType rootSelectionSet
                = some runtimeType)
      -> SelectionSetProbePathCoherent schema rootSelectionSet parentType
          selectionSet (responseName :: childPath) := by
  intro hobject hmem hlookup hchildValid hchildNormal hchildPath
    hrootPreservesRuntime
  exact
    SelectionSetProbePathCoherent.objectChild hobject hmem hlookup
      (fun hcomposite =>
        fieldHeadProbeRuntimeCoherent_of_child_pathCoherent hchildValid
          hchildNormal hcomposite hchildPath hrootPreservesRuntime)
      hchildPath

end GroundTypeNormalization

end NormalForm

end GraphQL
