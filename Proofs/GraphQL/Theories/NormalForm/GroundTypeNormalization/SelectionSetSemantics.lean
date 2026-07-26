import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.FieldSemantics
import Proofs.GraphQL.Theories.NormalForm.Shared.FieldMergeLookup

/-!
Selection-set semantic preservation for ground-type normalization.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

variable {ObjectRef : Type}

theorem normalizeSelectionSet_executeSelectionSet
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    : ∀ depth parentType (source : Execution.ResolverValue ObjectRef) selectionSet,
        objectTypeNameBool schema parentType = true
        -> (∃ runtimeType ref,
              source = .object runtimeType ref
              ∧ schema.typeIncludesObjectBool parentType runtimeType = true)
        -> selectionSetDirectiveFree selectionSet
        -> selectionSetSemanticsReady schema parentType selectionSet
        -> FieldMerge.fieldsInSetCanMerge schema parentType selectionSet
        -> Execution.executeSelectionSet schema resolvers variableValues depth
              parentType source
              (normalizeSelectionSet schema parentType selectionSet)
            = Execution.executeSelectionSet schema resolvers variableValues depth
                parentType source selectionSet := by
  intro depth parentType source selectionSet
  revert depth source
  induction parentType, selectionSet using normalizeSelectionSet.induct schema
    with
  | case1 parentType =>
      intro depth source _hobject _hsource _hfree _hready _hmerge
      simp [normalizeSelectionSet]
  | case2 parentType rest responseName fieldName arguments directives
      subselections hlookup _hrest =>
      intro depth source _hobject _hsource _hfree hready _hmerge
      have hlookupValid :
          selectionSetLookupValid schema parentType
            (Selection.field responseName fieldName arguments directives
              subselections :: rest) :=
        selectionSetLookupValid_of_selectionSetSemanticsReady
          (Selection.field responseName fieldName arguments directives
            subselections :: rest)
          hready
      exact False.elim
        (selectionSetLookupValid_field_head_lookup_none_false hlookupValid
          hlookup)
  | case3 parentType rest responseName fieldName arguments directives
      subselections fieldDefinition hlookup matching mergedSubselections
      returnType htailIH hobjectIH hpossibleIH =>
      intro depth source hobject hsource hfree hready hmerge
      have hheadFree :
          selectionDirectiveFree
            (Selection.field responseName fieldName arguments directives
              subselections) :=
        selectionSetDirectiveFree_head hfree
      have hdirectives : directives = [] := by
        simpa [selectionDirectiveFree] using hheadFree.1
      subst directives
      let mergedSubselections :=
        subselections
          ++ mergeSelectionSets
            (fieldSelectionsWithResponseNameInScope schema parentType responseName rest)
      have htailFree :
          selectionSetDirectiveFree rest :=
        selectionSetDirectiveFree_tail hfree
      have htailReady :
          selectionSetSemanticsReady schema parentType rest :=
        selectionSetSemanticsReady_tail hready
      have htailMerge :
          FieldMerge.fieldsInSetCanMerge schema parentType rest :=
        fieldsInSetCanMerge_tail schema parentType
          (Selection.field responseName fieldName arguments [] subselections)
          rest hmerge
      have hfilteredFree :
          selectionSetDirectiveFree
            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        withoutFieldSelectionsWithResponseName_directiveFree schema responseName rest
          htailFree
      have hfilteredReady :
          selectionSetSemanticsReady schema parentType
            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        selectionSetSemanticsReady_withoutFieldSelectionsWithResponseName schema
          responseName parentType rest htailReady
      have hfilteredMerge :
          FieldMerge.fieldsInSetCanMerge schema parentType
            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        fieldsInSetCanMerge_withoutFieldSelectionsWithResponseName schema responseName
          parentType rest htailMerge
      have htailEq :
          Execution.executeSelectionSet schema resolvers variableValues depth
            parentType source
            (normalizeSelectionSet schema parentType
              (withoutFieldSelectionsWithResponseName schema responseName rest))
          =
          Execution.executeSelectionSet schema resolvers variableValues depth
            parentType source
            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        htailIH depth source hobject hsource hfilteredFree hfilteredReady
          hfilteredMerge
      apply
        normalizeSelectionSet_executeSelectionSet_field_head_case_of_recursive
          schema resolvers variableValues hschema depth parentType source
          responseName fieldName arguments subselections rest fieldDefinition
          hobject hsource hfree hready hmerge hlookup
      · simp [normalizedFieldWithRest, normalizedField]
      · dsimp
        intro (childDepth : Nat) (runtimeType : Name) (ref : ObjectRef)
          hlt hchildObject hmergedFree
          _hmergedLookup hmergedReady hmergedMerge
        have hchildSource :
            ∃ childRuntime childRef,
              (Execution.ResolverValue.object runtimeType ref)
                =
                Execution.ResolverValue.object childRuntime childRef
              ∧ schema.typeIncludesObjectBool runtimeType childRuntime =
                true :=
          ⟨runtimeType, ref, rfl,
            typeIncludesObjectBool_self_of_objectTypeNameBool schema
              hchildObject⟩
        exact hpossibleIH runtimeType childDepth
          (Execution.ResolverValue.object runtimeType ref) hchildObject
          hchildSource hmergedFree hmergedReady hmergedMerge
      · exact htailEq
  | case4 parentType rest directives selectionSet happend =>
      intro depth source hobject hsource hfree hready hmerge
      have hheadFree :
          selectionDirectiveFree
            (Selection.inlineFragment none directives selectionSet) :=
        selectionSetDirectiveFree_head hfree
      have hdirectives : directives = [] := by
        simpa [selectionDirectiveFree] using hheadFree.1
      subst directives
      have htailFree :
          selectionSetDirectiveFree rest :=
        selectionSetDirectiveFree_tail hfree
      have hselectionFree :
          selectionSetDirectiveFree selectionSet := by
        simpa [selectionDirectiveFree] using hheadFree.2
      have happendFree :
          selectionSetDirectiveFree (selectionSet ++ rest) :=
        selectionSetDirectiveFree_append hselectionFree htailFree
      have hheadReady :
          selectionSemanticsReady schema parentType
            (Selection.inlineFragment none [] selectionSet) := by
        unfold selectionSetSemanticsReady at hready
        exact hready _ (by simp)
      have hselectionReady :
          selectionSetSemanticsReady schema parentType selectionSet := by
        simpa [selectionSemanticsReady] using hheadReady
      have htailReady :
          selectionSetSemanticsReady schema parentType rest :=
        selectionSetSemanticsReady_tail hready
      have happendReady :
          selectionSetSemanticsReady schema parentType
            (selectionSet ++ rest) :=
        selectionSetSemanticsReady_append hselectionReady htailReady
      have happendMerge :
          FieldMerge.fieldsInSetCanMerge schema parentType
            (selectionSet ++ rest) :=
        fieldsInSetCanMerge_inlineFragment_none_flatten schema parentType
          selectionSet rest hmerge
      have happendEq :
          Execution.executeSelectionSet schema resolvers variableValues depth
            parentType source
            (normalizeSelectionSet schema parentType (selectionSet ++ rest))
          =
          Execution.executeSelectionSet schema resolvers variableValues depth
            parentType source (selectionSet ++ rest) :=
        happend depth source hobject hsource happendFree happendReady
          happendMerge
      exact normalizeSelectionSet_executeSelectionSet_inlineFragment_none_case
        schema resolvers variableValues depth parentType source selectionSet
        rest happendEq
  | case5 parentType rest typeCondition directives selectionSet hoverlap
      _hrest happend =>
      intro depth source hobject hsource hfree hready hmerge
      have hheadFree :
          selectionDirectiveFree
            (Selection.inlineFragment (some typeCondition) directives
              selectionSet) :=
        selectionSetDirectiveFree_head hfree
      have hdirectives : directives = [] := by
        simpa [selectionDirectiveFree] using hheadFree.1
      subst directives
      have htailFree :
          selectionSetDirectiveFree rest :=
        selectionSetDirectiveFree_tail hfree
      have hselectionFree :
          selectionSetDirectiveFree selectionSet := by
        simpa [selectionDirectiveFree] using hheadFree.2
      have happendFree :
          selectionSetDirectiveFree (selectionSet ++ rest) :=
        selectionSetDirectiveFree_append hselectionFree htailFree
      have hheadReady :
          selectionSemanticsReady schema parentType
            (Selection.inlineFragment (some typeCondition) [] selectionSet) := by
        unfold selectionSetSemanticsReady at hready
        exact hready _ (by simp)
      have hheadReadyPair :
          selectionSetLookupValid schema typeCondition selectionSet
            ∧ (schema.typesOverlapBool parentType typeCondition = true ->
              selectionSetSemanticsReady schema parentType selectionSet) := by
        simpa [selectionSemanticsReady] using hheadReady
      have hselectionTypeLookup :
          selectionSetLookupValid schema typeCondition selectionSet := by
        exact hheadReadyPair.1
      have hselectionReady :
          selectionSetSemanticsReady schema parentType selectionSet :=
        hheadReadyPair.2 hoverlap
      have htailReady :
          selectionSetSemanticsReady schema parentType rest :=
        selectionSetSemanticsReady_tail hready
      have happendReady :
          selectionSetSemanticsReady schema parentType
            (selectionSet ++ rest) :=
        selectionSetSemanticsReady_append hselectionReady htailReady
      have hselectionParentLookup :
          selectionSetLookupValid schema parentType selectionSet :=
        selectionSetLookupValid_of_selectionSetSemanticsReady selectionSet
          hselectionReady
      have htailLookup :
          selectionSetLookupValid schema parentType rest :=
        selectionSetLookupValid_of_selectionSetSemanticsReady rest htailReady
      have hparentObject :
          schema.objectType parentType :=
        objectType_of_objectTypeNameBool_eq_true schema hobject
      have happendMerge :
          FieldMerge.fieldsInSetCanMerge schema parentType
            (selectionSet ++ rest) :=
        fieldsInSetCanMerge_inlineFragment_some_overlap_flatten_object
          schema parentType typeCondition selectionSet rest hschema
          hparentObject hoverlap hselectionParentLookup hselectionTypeLookup
          htailLookup hmerge
      have happendEq :
          Execution.executeSelectionSet schema resolvers variableValues depth
            parentType source
            (normalizeSelectionSet schema parentType (selectionSet ++ rest))
          =
          Execution.executeSelectionSet schema resolvers variableValues depth
            parentType source (selectionSet ++ rest) :=
        happend depth source hobject hsource happendFree happendReady
          happendMerge
      exact normalizeSelectionSet_executeSelectionSet_inlineFragment_some_overlap_case
        schema resolvers variableValues depth parentType typeCondition source
        selectionSet rest hobject hsource hoverlap happendEq
  | case6 parentType rest typeCondition directives selectionSet hoverlap
      hrest =>
      intro depth source hobject hsource hfree hready hmerge
      have hheadFree :
          selectionDirectiveFree
            (Selection.inlineFragment (some typeCondition) directives
              selectionSet) :=
        selectionSetDirectiveFree_head hfree
      have hdirectives : directives = [] := by
        simpa [selectionDirectiveFree] using hheadFree.1
      subst directives
      have htailFree :
          selectionSetDirectiveFree rest :=
        selectionSetDirectiveFree_tail hfree
      have htailReady :
          selectionSetSemanticsReady schema parentType rest :=
        selectionSetSemanticsReady_tail hready
      have htailMerge :
          FieldMerge.fieldsInSetCanMerge schema parentType rest :=
        fieldsInSetCanMerge_tail schema parentType
          (Selection.inlineFragment (some typeCondition) [] selectionSet)
          rest hmerge
      have hrestEq :
          Execution.executeSelectionSet schema resolvers variableValues depth
            parentType source
            (normalizeSelectionSet schema parentType rest)
          =
          Execution.executeSelectionSet schema resolvers variableValues depth
            parentType source rest :=
        hrest depth source hobject hsource htailFree htailReady htailMerge
      have hoverlapFalse :
          schema.typesOverlapBool parentType typeCondition = false := by
        cases hmatch : schema.typesOverlapBool parentType typeCondition
        · rfl
        · exact False.elim (hoverlap hmatch)
      exact normalizeSelectionSet_executeSelectionSet_inlineFragment_some_noOverlap_case
        schema resolvers variableValues depth parentType typeCondition source
        selectionSet rest hsource hoverlapFalse hrestEq

end GroundTypeNormalization

end NormalForm

end GraphQL
