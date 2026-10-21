import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Normality
import Proofs.GraphQL.Theories.NormalForm.Shared.FieldProjection
import Proofs.GraphQL.Theories.NormalForm.Shared.SemanticReadiness.RuntimeSources

/-! Normalized fields retain recursive groups of declared-scope sources. -/

namespace GraphQL.NormalForm.GroundTypeNormalization

private theorem collectFields_possibleNormalizations_source
    (schema : Schema) (parentType : Name)
    : ∀ possibleTypes selectionSet field,
        field
          ∈ FieldMerge.collectFields schema parentType
              (possibleTypeNormalizations schema possibleTypes selectionSet)
        -> ∃ objectType,
            objectType ∈ possibleTypes
            ∧ field
              ∈ FieldMerge.collectFields schema objectType
                  (normalizeSelectionSet schema objectType selectionSet)
  | [], selectionSet, field, hfield => by
      simp [possibleTypeNormalizations, FieldMerge.collectFields] at hfield
  | objectType :: rest, selectionSet, field, hfield => by
      cases hnormalized : normalizeSelectionSet schema objectType selectionSet with
      | nil =>
          simp [possibleTypeNormalizations, hnormalized] at hfield
          rcases collectFields_possibleNormalizations_source schema parentType rest
            selectionSet field hfield with ⟨runtime, hruntime, hfield⟩
          exact ⟨runtime, List.mem_cons_of_mem _ hruntime, hfield⟩
      | cons selection tail =>
          simp [possibleTypeNormalizations, hnormalized, FieldMerge.collectFields] at hfield
          rcases hfield with hhead | htail
          · exact ⟨objectType, by simp, by simpa [hnormalized] using hhead⟩
          · rcases collectFields_possibleNormalizations_source schema parentType rest
              selectionSet field htail with ⟨runtime, hruntime, hfield⟩
            exact ⟨runtime, List.mem_cons_of_mem _ hruntime, hfield⟩

theorem normalizeSelectionSet_fieldProjection
    (schema : Schema) (hschema : SchemaWellFormedness.schemaWellFormed schema)
    : ∀ parentType selectionSet sources,
        schema.objectType parentType
        -> selectionSetDirectiveFree selectionSet
        -> selectionSetSemanticsReady schema parentType selectionSet
        -> runtimeMergeSources schema parentType selectionSet sources
        -> ∀ target,
            target
              ∈ FieldMerge.collectFields schema parentType
                  (normalizeSelectionSet schema parentType selectionSet)
            -> ∃ group, group ⊆ sources ∧ FieldProjection schema group target := by
  intro parentType selectionSet
  induction parentType, selectionSet using normalizeSelectionSet.induct schema with
  | case1 parentType =>
      intro sources _ _ _ _ target htarget
      simp [normalizeSelectionSet, FieldMerge.collectFields] at htarget
  | case2 parentType rest responseName fieldName arguments directives children hlookup _
    =>
      intro sources _ _ hready _ target _
      exact False.elim (runtimeLookupValid_field_head_lookup_none_false
        (selectionSetLookupValid_of_selectionSetSemanticsReady _ hready) hlookup)
  | case3 parentType rest responseName fieldName arguments directives children
      definition hlookup matching merged returnType htailIH hobjectIH hpossibleIH =>
      intro sources hobject hfree hready hsource target htarget
      have hheadFree := selectionSetDirectiveFree_head hfree
      have hdirectives : directives = [] := hheadFree.1
      subst directives
      have htailFree := selectionSetDirectiveFree_tail hfree
      have hfilteredFree := withoutFieldSelectionsWithResponseName_directiveFree
        schema responseName rest htailFree
      have hfilteredReady := selectionSetSemanticsReady_withoutFieldSelectionsWithResponseName
        schema responseName parentType rest (selectionSetSemanticsReady_tail hready)
      have hfilteredSource := runtimeMergeSources_without schema responseName parentType rest
        (runtimeMergeSources_tail hsource)
      let body := if objectTypeNameBool schema returnType then
          normalizeSelectionSet schema returnType merged
        else possibleTypeNormalizations schema (schema.getPossibleTypes returnType) merged
      rw [normalizeSelectionSet.eq_2, hlookup] at htarget
      change target ∈ FieldMerge.collectFields schema parentType
        (Selection.field responseName fieldName arguments [] body ::
          normalizeSelectionSet schema parentType
            (withoutFieldSelectionsWithResponseName schema responseName rest)) at htarget
      simp only [FieldMerge.collectFields, hlookup, List.singleton_append, List.mem_cons]
        at htarget
      rcases htarget with rfl | htarget
      · let parents := runtimeMergeParentSources schema parentType responseName sources
        have hparents := runtimeMergeSources_fieldHead_parents schema hschema hsource hlookup
        refine ⟨
          parents,
          ?_,
          .intro hparents.1 (fun source hmem => (hparents.2 source hmem).1)
            (fun source hmem => (hparents.2 source hmem).2) ?_
        ⟩
        · intro source hmem
          exact (List.mem_filter.mp hmem).1
        · intro child hchild
          have hmergedFree : selectionSetDirectiveFree merged := by
            dsimp [merged, matching]
            exact selectionSetDirectiveFree_append hheadFree.2
              (selectionSetDirectiveFree_mergeSelectionSets
                (fieldSelectionsWithResponseNameInScope_directiveFree schema parentType
                  responseName rest htailFree))
          have hbranch (runtime : Name) (hruntime : schema.objectType runtime)
              (hinclude : schema.typeIncludesObjectBool definition.outputType.namedType runtime = true)
              (hchild : child ∈ FieldMerge.collectFields schema runtime
                (normalizeSelectionSet schema runtime merged))
              : FieldProjectionSources schema parents child := by
            have hchildReady := runtimeMergeSource_fieldHead_semanticsReady schema
              ⟨sources, hsource⟩ hready hlookup hinclude
            have hchildSource := runtimeMergeSources_fieldHead_merged schema hschema
              hsource hlookup hinclude
            rcases hpossibleIH runtime _ hruntime hmergedFree hchildReady hchildSource
                child hchild with ⟨group, hsubset, hprojection⟩
            exact .intro hsubset hprojection
          by_cases hreturn : objectTypeNameBool schema returnType = true
          · apply hbranch returnType
              (objectType_of_objectTypeNameBool_eq_true schema hreturn)
            · exact object_typeIncludesObjectBool_self schema
                (objectType_of_objectTypeNameBool_eq_true schema hreturn)
            · simpa [body, hreturn] using hchild
          · have hreturnFalse : objectTypeNameBool schema returnType = false := by
              cases h : objectTypeNameBool schema returnType <;> simp_all
            have hchild' : child ∈ FieldMerge.collectFields schema returnType
                (possibleTypeNormalizations schema (schema.getPossibleTypes returnType) merged) := by
              simpa [body, hreturnFalse] using hchild
            rcases collectFields_possibleNormalizations_source schema returnType _ _ _ hchild'
              with ⟨runtime, hruntime, hchild⟩
            exact hbranch runtime
              (SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects hschema
                returnType runtime hruntime)
              (List.contains_iff_mem.mpr hruntime) hchild
      · exact htailIH sources hobject hfilteredFree hfilteredReady hfilteredSource
          target htarget
  | case4 parentType rest directives children happend =>
      intro sources hobject hfree hready hsource target htarget
      have hheadFree := selectionSetDirectiveFree_head hfree
      have hdirectives : directives = [] := hheadFree.1
      subst directives
      have hheadReady : selectionSemanticsReady schema parentType
          (Selection.inlineFragment none [] children) := by
        unfold selectionSetSemanticsReady at hready
        exact hready _ (by simp)
      have hbodyReady : selectionSetSemanticsReady schema parentType children := by
        simpa [selectionSemanticsReady] using hheadReady
      apply happend sources hobject
        (selectionSetDirectiveFree_append hheadFree.2
          (selectionSetDirectiveFree_tail hfree))
        (selectionSetSemanticsReady_append hbodyReady
          (selectionSetSemanticsReady_tail hready))
        (runtimeMergeSources_inlineFragment_flatten schema parentType none children rest
          (by simp) hsource) target
      simpa [normalizeSelectionSet] using htarget
  | case5 parentType rest condition directives children hoverlap _ happend =>
      intro sources hobject hfree hready hsource target htarget
      have hheadFree := selectionSetDirectiveFree_head hfree
      have hdirectives : directives = [] := hheadFree.1
      subst directives
      have hheadReady : selectionSemanticsReady schema parentType
          (Selection.inlineFragment (some condition) [] children) := by
        unfold selectionSetSemanticsReady at hready
        exact hready _ (by simp)
      have hbodyReady : selectionSetSemanticsReady schema parentType children := by
        have hpair : selectionSetLookupValid schema condition children ∧
          (schema.typesOverlapBool parentType condition = true ->
            selectionSetSemanticsReady schema parentType children) := by
          simpa [selectionSemanticsReady] using hheadReady
        exact hpair.2 hoverlap
      apply happend sources hobject
        (selectionSetDirectiveFree_append hheadFree.2
          (selectionSetDirectiveFree_tail hfree))
        (selectionSetSemanticsReady_append hbodyReady
          (selectionSetSemanticsReady_tail hready))
        (runtimeMergeSources_inlineFragment_flatten schema parentType (some condition)
          children rest (by intro _ h; cases h; exact hoverlap) hsource) target
      simpa [normalizeSelectionSet, hoverlap] using htarget
  | case6 parentType rest condition directives children hoverlap hrest =>
      intro sources hobject hfree hready hsource target htarget
      apply hrest sources hobject (selectionSetDirectiveFree_tail hfree)
        (selectionSetSemanticsReady_tail hready) (runtimeMergeSources_tail hsource) target
      simpa [normalizeSelectionSet, hoverlap] using htarget

theorem normalizeSelectionSet_fieldsForNameCanMerge (schema : Schema)
    (hschema : SchemaWellFormedness.schemaWellFormed schema) {leftType rightType : Name}
    {selectionSet : List Selection} {sources : List FieldMerge.ScopedField}
    {left right : FieldMerge.ScopedField} (hleftObject : schema.objectType leftType)
    (hrightObject : schema.objectType rightType)
    (hfree : selectionSetDirectiveFree selectionSet)
    (hleftReady : selectionSetSemanticsReady schema leftType selectionSet)
    (hrightReady : selectionSetSemanticsReady schema rightType selectionSet)
    (hleftSource : runtimeMergeSources schema leftType selectionSet sources)
    (hrightSource : runtimeMergeSources schema rightType selectionSet sources)
    (hleft
      : left
        ∈ FieldMerge.collectFields schema leftType
            (normalizeSelectionSet schema leftType selectionSet))
    (hright
      : right
        ∈ FieldMerge.collectFields schema rightType
            (normalizeSelectionSet schema rightType selectionSet))
    (hresponse : left.responseName = right.responseName)
    : FieldMerge.fieldsForNameCanMerge schema left right := by
  rcases normalizeSelectionSet_fieldProjection schema hschema leftType selectionSet sources
    hleftObject hfree hleftReady hleftSource left hleft with ⟨leftGroup, hleftSubset, hleft⟩
  rcases normalizeSelectionSet_fieldProjection schema hschema rightType selectionSet sources
    hrightObject hfree hrightReady hrightSource right hright with ⟨rightGroup, hrightSubset, hright⟩
  apply FieldProjection.canMerge schema left right hleft hright hresponse
  intro sourceLeft hsourceLeft sourceRight hsourceRight hsourceResponse
  have hsubset : leftGroup ++ rightGroup ⊆ sources := by
    intro source hsource
    exact (List.mem_append.mp hsource).elim
      (fun h => hleftSubset h) (fun h => hrightSubset h)
  exact hleftSource.2.1 _ (hsubset hsourceLeft) _ (hsubset hsourceRight) hsourceResponse

theorem normalizeSelectionSet_fieldsInSetCanMerge
    (schema : Schema) (hschema : SchemaWellFormedness.schemaWellFormed schema)
    {parentType : Name} {selectionSet : List Selection}
    (hobject : schema.objectType parentType)
    (hfree : selectionSetDirectiveFree selectionSet)
    (hready : selectionSetSemanticsReady schema parentType selectionSet)
    (hsource : runtimeMergeSource schema parentType selectionSet)
    : FieldMerge.fieldsInSetCanMerge schema parentType
        (normalizeSelectionSet schema parentType selectionSet) := by
  rcases hsource with ⟨sources, hsource⟩
  refine .intro parentType _ ?_
  dsimp
  intro left hleft right hright hresponse
  exact normalizeSelectionSet_fieldsForNameCanMerge schema hschema hobject hobject hfree
    hready hready hsource hsource hleft hright hresponse

end GraphQL.NormalForm.GroundTypeNormalization
