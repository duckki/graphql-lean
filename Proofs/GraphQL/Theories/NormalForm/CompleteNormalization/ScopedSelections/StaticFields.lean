import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.ScopedSelections.Basics

/-! Static-field collection facts for complete-normalization scoped selections. -/

namespace GraphQL

namespace NormalForm

namespace CompleteNormalization

set_option linter.unusedSimpArgs false in
theorem fieldSelectionsWithResponseNameInScope_staticCollectForGround_scoped
    (schema : Schema) (variables : List BoolVar)
    (filterParent lookupParent groundType responseName : Name)
    (boolCase : BoolCase)
    : ∀ selectionSet,
        fieldSelectionsWithResponseNameInScope schema filterParent responseName
          (staticCollectForGround schema variables lookupParent
            groundType boolCase selectionSet)
        = staticCollectCompleteScopedSelectionSet schema variables groundType
            boolCase
            (staticScopedFieldsWithResponseName schema boolCase lookupParent
              groundType responseName selectionSet)
  | [] => by
      simp [fieldSelectionsWithResponseNameInScope, staticCollectForGround,
        staticScopedFieldsWithResponseName,
        staticCollectCompleteScopedSelectionSet]
  | selection :: rest => by
      cases selection with
      | field fieldResponseName fieldName arguments directives selectionSet =>
          cases hallow :
              directivesAllowIn boolCase directives
          · simp [staticCollectForGround,
              staticScopedFieldsWithResponseName, hallow,
              fieldSelectionsWithResponseNameInScope_staticCollectForGround_scoped
                schema variables filterParent lookupParent groundType responseName
                boolCase rest]
          · cases hresponse : fieldResponseName == responseName
            · cases hlookup : schema.lookupField lookupParent fieldName with
              | none =>
                  cases selectionSet with
                  | nil =>
                      simp [staticCollectForGround,
                        staticScopedFieldsWithResponseName,
                        staticCollectCompleteScopedSelectionSet,
                        staticCollectCompleteScopedSelection,
                        fieldSelectionsWithResponseNameInScope, hallow, hresponse,
                        hlookup,
                        fieldSelectionsWithResponseNameInScope_staticCollectForGround_scoped
                          schema variables filterParent lookupParent groundType
                          responseName boolCase rest]
                  | cons child childRest =>
                        cases hnormalized :
                            staticCollectForGround schema variables
                              lookupParent lookupParent boolCase
                              (child :: childRest) with
                      | nil =>
                          simp [staticCollectForGround,
                            staticScopedFieldsWithResponseName,
                            staticCollectCompleteScopedSelectionSet,
                            staticCollectCompleteScopedSelection,
                            fieldSelectionsWithResponseNameInScope, hallow, hresponse,
                            hlookup, hnormalized,
                            fieldSelectionsWithResponseNameInScope_staticCollectForGround_scoped
                              schema variables filterParent lookupParent
                              groundType responseName boolCase rest]
                      | cons normalizedChild normalizedRest =>
                          simp [staticCollectForGround,
                            staticScopedFieldsWithResponseName,
                            staticCollectCompleteScopedSelectionSet,
                            staticCollectCompleteScopedSelection,
                            fieldSelectionsWithResponseNameInScope, hallow, hresponse,
                            hlookup, hnormalized,
                            fieldSelectionsWithResponseNameInScope_staticCollectForGround_scoped
                              schema variables filterParent lookupParent
                              groundType responseName boolCase rest]
                | some fieldDefinition =>
                    cases hnormalized :
                        normalizeBoolCaseForType schema boolCase
                          fieldDefinition.outputType.namedType
                          selectionSet <;>
                      simp [staticCollectForGround,
                        staticScopedFieldsWithResponseName,
                        staticCollectCompleteScopedSelectionSet,
                        staticCollectCompleteScopedSelection,
                        fieldSelectionsWithResponseNameInScope, hallow, hresponse,
                        hlookup, hnormalized,
                        fieldSelectionsWithResponseNameInScope_staticCollectForGround_scoped
                          schema variables filterParent lookupParent
                          groundType responseName boolCase rest]
            · cases hlookup : schema.lookupField lookupParent fieldName with
              | none =>
                  cases selectionSet with
                  | nil =>
                      simp [staticCollectForGround,
                        staticScopedFieldsWithResponseName,
                        staticCollectCompleteScopedSelectionSet,
                        staticCollectCompleteScopedSelection,
                        fieldSelectionsWithResponseNameInScope, hallow, hresponse,
                        hlookup,
                        fieldSelectionsWithResponseNameInScope_staticCollectForGround_scoped
                          schema variables filterParent lookupParent groundType
                          responseName boolCase rest]
                  | cons child childRest =>
                        cases hnormalized :
                            staticCollectForGround schema variables
                              lookupParent lookupParent boolCase
                              (child :: childRest) with
                      | nil =>
                          simp [staticCollectForGround,
                            staticScopedFieldsWithResponseName,
                            staticCollectCompleteScopedSelectionSet,
                            staticCollectCompleteScopedSelection,
                            fieldSelectionsWithResponseNameInScope, hallow, hresponse,
                            hlookup, hnormalized,
                            fieldSelectionsWithResponseNameInScope_staticCollectForGround_scoped
                              schema variables filterParent lookupParent
                              groundType responseName boolCase rest]
                      | cons normalizedChild normalizedRest =>
                          simp [staticCollectForGround,
                            staticScopedFieldsWithResponseName,
                            staticCollectCompleteScopedSelectionSet,
                            staticCollectCompleteScopedSelection,
                            fieldSelectionsWithResponseNameInScope, hallow, hresponse,
                            hlookup, hnormalized,
                            fieldSelectionsWithResponseNameInScope_staticCollectForGround_scoped
                              schema variables filterParent lookupParent
                              groundType responseName boolCase rest]
                | some fieldDefinition =>
                    cases hnormalized :
                        normalizeBoolCaseForType schema boolCase
                          fieldDefinition.outputType.namedType
                          selectionSet <;>
                      simp [staticCollectForGround,
                        staticScopedFieldsWithResponseName,
                        staticCollectCompleteScopedSelectionSet,
                        staticCollectCompleteScopedSelection,
                        fieldSelectionsWithResponseNameInScope, hallow, hresponse,
                        hlookup, hnormalized,
                        fieldSelectionsWithResponseNameInScope_staticCollectForGround_scoped
                          schema variables filterParent lookupParent
                          groundType responseName boolCase rest]
      | inlineFragment typeCondition directives selectionSet =>
          cases typeCondition with
          | none =>
              cases hallow :
                  directivesAllowIn boolCase directives
              · simp [staticCollectForGround,
                  staticScopedFieldsWithResponseName, hallow,
                  fieldSelectionsWithResponseNameInScope_staticCollectForGround_scoped
                    schema variables filterParent lookupParent groundType
                    responseName boolCase rest]
              · simp [staticCollectForGround,
                  staticScopedFieldsWithResponseName, hallow,
                  fieldSelectionsWithResponseNameInScope_append,
                  staticCollectCompleteScopedSelectionSet_append,
                  fieldSelectionsWithResponseNameInScope_staticCollectForGround_scoped
                    schema variables filterParent lookupParent groundType
                    responseName boolCase selectionSet,
                  fieldSelectionsWithResponseNameInScope_staticCollectForGround_scoped
                    schema variables filterParent lookupParent groundType
                    responseName boolCase rest]
          | some typeCondition =>
              cases hbranch :
                  directivesAllowIn boolCase directives
                    && schema.typeIncludesObjectBool typeCondition groundType
              · simp [staticCollectForGround,
                  staticScopedFieldsWithResponseName, hbranch,
                  fieldSelectionsWithResponseNameInScope_staticCollectForGround_scoped
                    schema variables filterParent lookupParent groundType
                    responseName boolCase rest]
              · simp [staticCollectForGround,
                  staticScopedFieldsWithResponseName, hbranch,
                  fieldSelectionsWithResponseNameInScope_append,
                  staticCollectCompleteScopedSelectionSet_append,
                  fieldSelectionsWithResponseNameInScope_staticCollectForGround_scoped
                    schema variables filterParent typeCondition groundType
                    responseName boolCase selectionSet,
                  fieldSelectionsWithResponseNameInScope_staticCollectForGround_scoped
                    schema variables filterParent lookupParent groundType
                    responseName boolCase rest]

theorem fieldSelectionsWithResponseNameInScope_staticCollectCompleteScopedSelectionSet
    (schema : Schema) (variables : List BoolVar)
    (filterParent groundType responseName : Name)
    (boolCase : BoolCase)
    : ∀ scopedSelections,
        fieldSelectionsWithResponseNameInScope schema filterParent responseName
          (staticCollectCompleteScopedSelectionSet schema variables groundType
            boolCase scopedSelections)
        = staticCollectCompleteScopedSelectionSet schema variables groundType
            boolCase
            (completeScopedSelectionSetStaticFieldsWithResponseName schema
              boolCase groundType responseName scopedSelections)
  | [] => by
      simp [fieldSelectionsWithResponseNameInScope,
        staticCollectCompleteScopedSelectionSet,
        completeScopedSelectionSetStaticFieldsWithResponseName]
  | scopedSelection :: rest => by
      cases scopedSelection with
      | mk lookupParent selection =>
          have hhead :=
            fieldSelectionsWithResponseNameInScope_staticCollectForGround_scoped
              schema variables filterParent lookupParent groundType
              responseName boolCase [selection]
          have hrest :=
            fieldSelectionsWithResponseNameInScope_staticCollectCompleteScopedSelectionSet
              schema variables filterParent groundType responseName boolCase
              rest
          rw [staticCollectCompleteScopedSelectionSet]
          rw [fieldSelectionsWithResponseNameInScope_append]
          change
            fieldSelectionsWithResponseNameInScope schema filterParent responseName
                (staticCollectForGround schema variables
                  lookupParent groundType boolCase [selection])
              ++
            fieldSelectionsWithResponseNameInScope schema filterParent responseName
                (staticCollectCompleteScopedSelectionSet schema variables
                  groundType boolCase rest)
              =
            staticCollectCompleteScopedSelectionSet schema variables groundType
              boolCase
              (completeScopedSelectionSetStaticFieldsWithResponseName schema
                boolCase groundType responseName
                ({ lookupParent := lookupParent, selection := selection }
                  :: rest))
          rw [hhead, hrest]
          cases selection with
          | field fieldResponseName fieldName arguments directives selectionSet =>
              cases hallow :
                  directivesAllowIn boolCase directives <;>
                cases hresponse : fieldResponseName == responseName <;>
                  cases hlookup : schema.lookupField lookupParent fieldName <;>
                    simp [staticCollectCompleteScopedSelectionSet,
                      staticCollectCompleteScopedSelection,
                      staticCollectForGround,
                      staticScopedFieldsWithResponseName,
                      completeScopedSelectionSetStaticFieldsWithResponseName,
                      hallow, hresponse, hlookup]
          | inlineFragment typeCondition directives selectionSet =>
              cases typeCondition with
              | none =>
                  cases hallow :
                      directivesAllowIn boolCase directives <;>
                    simp [staticCollectCompleteScopedSelectionSet,
                      staticCollectCompleteScopedSelectionSet_append,
                      staticScopedFieldsWithResponseName,
                      completeScopedSelectionSetStaticFieldsWithResponseName,
                      hallow]
              | some typeCondition =>
                  cases hbranch :
                      directivesAllowIn boolCase directives
                        && schema.typeIncludesObjectBool typeCondition
                          groundType <;>
                    simp [staticCollectCompleteScopedSelectionSet,
                      staticCollectCompleteScopedSelectionSet_append,
                      staticScopedFieldsWithResponseName,
                      completeScopedSelectionSetStaticFieldsWithResponseName,
                      hbranch]

theorem staticScopedFieldsWithResponseName_lookupValid
    (schema : Schema) (boolCase : BoolCase)
    (lookupParent groundType responseName : Name)
    : ∀ selectionSet,
        selectionSetLookupValid schema lookupParent selectionSet
        -> completeScopedSelectionSetLookupValid schema
            (staticScopedFieldsWithResponseName schema boolCase lookupParent
              groundType responseName selectionSet)
  | [], _hvalid => by
      simp [staticScopedFieldsWithResponseName,
        completeScopedSelectionSetLookupValid]
  | selection :: rest, hvalid => by
      have hheadValid :
          selectionLookupValid schema lookupParent selection :=
        selectionSetLookupValid_head hvalid
      have htailValid :
          selectionSetLookupValid schema lookupParent rest :=
        selectionSetLookupValid_tail hvalid
      have hrest :=
        staticScopedFieldsWithResponseName_lookupValid schema boolCase
          lookupParent groundType responseName rest htailValid
      cases selection with
      | field fieldResponseName fieldName arguments directives selectionSet =>
          cases hallow :
              directivesAllowIn boolCase directives
          · simpa [staticScopedFieldsWithResponseName, hallow] using hrest
          · cases hresponse : fieldResponseName == responseName
            · simpa [staticScopedFieldsWithResponseName, hallow, hresponse]
                using hrest
            · intro scopedSelection hmem
              simp [staticScopedFieldsWithResponseName, hallow, hresponse]
                at hmem
              rcases hmem with hhead | htail
              · subst scopedSelection
                exact hheadValid
              · exact hrest scopedSelection htail
      | inlineFragment typeCondition directives selectionSet =>
          cases typeCondition with
          | none =>
              cases hallow :
                  directivesAllowIn boolCase directives
              · simpa [staticScopedFieldsWithResponseName, hallow]
                  using hrest
              · have hbodyValid :
                    selectionSetLookupValid schema lookupParent
                      selectionSet := by
                  simpa [selectionLookupValid] using hheadValid
                have hbody :=
                  staticScopedFieldsWithResponseName_lookupValid schema
                    boolCase lookupParent groundType responseName
                    selectionSet hbodyValid
                simpa [staticScopedFieldsWithResponseName, hallow] using
                  completeScopedSelectionSetLookupValid_append hbody hrest
          | some typeCondition =>
              cases hbranch :
                  directivesAllowIn boolCase directives
                    && schema.typeIncludesObjectBool typeCondition groundType
              · simpa [staticScopedFieldsWithResponseName, hbranch]
                  using hrest
              · have hbodyValid :
                    selectionSetLookupValid schema typeCondition
                      selectionSet := by
                  simpa [selectionLookupValid] using hheadValid
                have hbody :=
                  staticScopedFieldsWithResponseName_lookupValid schema
                    boolCase typeCondition groundType responseName
                    selectionSet hbodyValid
                simpa [staticScopedFieldsWithResponseName, hbranch] using
                  completeScopedSelectionSetLookupValid_append hbody hrest

theorem staticScopedFieldsWithResponseName_groundApplies
    (schema : Schema) (boolCase : BoolCase)
    (lookupParent groundType responseName : Name)
    : ∀ selectionSet,
        schema.typeIncludesObjectBool lookupParent groundType = true
        -> completeScopedSelectionSetGroundApplies schema groundType
            (staticScopedFieldsWithResponseName schema boolCase lookupParent
              groundType responseName selectionSet)
  | [], _hincludes => by
      simp [staticScopedFieldsWithResponseName,
        completeScopedSelectionSetGroundApplies]
  | selection :: rest, hincludes => by
      have hrest :=
        staticScopedFieldsWithResponseName_groundApplies schema boolCase
          lookupParent groundType responseName rest hincludes
      cases selection with
      | field fieldResponseName fieldName arguments directives selectionSet =>
          cases hallow :
              directivesAllowIn boolCase directives
          · simpa [staticScopedFieldsWithResponseName, hallow] using hrest
          · cases hresponse : fieldResponseName == responseName
            · simpa [staticScopedFieldsWithResponseName, hallow, hresponse]
                using hrest
            · intro scopedSelection hmem
              simp [staticScopedFieldsWithResponseName, hallow, hresponse]
                at hmem
              rcases hmem with hhead | htail
              · subst scopedSelection
                exact hincludes
              · exact hrest scopedSelection htail
      | inlineFragment typeCondition directives selectionSet =>
          cases typeCondition with
          | none =>
              cases hallow :
                  directivesAllowIn boolCase directives
              · simpa [staticScopedFieldsWithResponseName, hallow]
                  using hrest
              · have hbody :=
                  staticScopedFieldsWithResponseName_groundApplies schema
                    boolCase lookupParent groundType responseName
                    selectionSet hincludes
                simpa [staticScopedFieldsWithResponseName, hallow] using
                  completeScopedSelectionSetGroundApplies_append hbody hrest
          | some typeCondition =>
              cases hbranch :
                  directivesAllowIn boolCase directives
                    && schema.typeIncludesObjectBool typeCondition groundType
              · simpa [staticScopedFieldsWithResponseName, hbranch]
                  using hrest
              · have htypeIncludes :
                    schema.typeIncludesObjectBool typeCondition groundType =
                      true := by
                  cases hallow :
                      directivesAllowIn boolCase directives
                  · simp [hallow] at hbranch
                  · simpa [hallow] using hbranch
                have hbody :=
                  staticScopedFieldsWithResponseName_groundApplies schema
                    boolCase typeCondition groundType responseName
                    selectionSet htypeIncludes
                simpa [staticScopedFieldsWithResponseName, hbranch] using
                  completeScopedSelectionSetGroundApplies_append hbody hrest

theorem completeScopedSelectionSetStaticFieldsWithResponseName_lookupValid
    (schema : Schema) (boolCase : BoolCase)
    (groundType responseName : Name)
    : ∀ scopedSelections,
        completeScopedSelectionSetLookupValid schema scopedSelections
        -> completeScopedSelectionSetLookupValid schema
            (completeScopedSelectionSetStaticFieldsWithResponseName schema
              boolCase groundType responseName scopedSelections)
  | [], _hvalid => by
      simp [completeScopedSelectionSetStaticFieldsWithResponseName,
        completeScopedSelectionSetLookupValid]
  | scopedSelection :: rest, hvalid => by
      have hheadValid :
          selectionLookupValid schema scopedSelection.lookupParent
            scopedSelection.selection :=
        hvalid scopedSelection (by simp)
      have htailValid :
          completeScopedSelectionSetLookupValid schema rest := by
        intro candidate hcandidate
        exact hvalid candidate (by simp [hcandidate])
      have hrest :=
        completeScopedSelectionSetStaticFieldsWithResponseName_lookupValid
          schema boolCase groundType responseName rest htailValid
      cases scopedSelection with
      | mk lookupParent selection =>
          cases selection with
          | field fieldResponseName fieldName arguments directives selectionSet =>
              cases hallow :
                  directivesAllowIn boolCase directives
              · simpa [completeScopedSelectionSetStaticFieldsWithResponseName,
                  hallow] using hrest
              · cases hresponse : fieldResponseName == responseName
                · simpa [completeScopedSelectionSetStaticFieldsWithResponseName,
                    hallow, hresponse] using hrest
                · intro candidate hcandidate
                  simp [completeScopedSelectionSetStaticFieldsWithResponseName,
                    hallow, hresponse] at hcandidate
                  rcases hcandidate with hcandidate | hcandidate
                  · subst candidate
                    exact hheadValid
                  · exact hrest candidate hcandidate
          | inlineFragment typeCondition directives selectionSet =>
              cases typeCondition with
              | none =>
                  cases hallow :
                      directivesAllowIn boolCase directives
                  · simpa [completeScopedSelectionSetStaticFieldsWithResponseName,
                      hallow] using hrest
                  · have hbodyValid :
                        selectionSetLookupValid schema lookupParent
                          selectionSet := by
                      simpa [selectionLookupValid] using hheadValid
                    have hbody :=
                      staticScopedFieldsWithResponseName_lookupValid schema
                        boolCase lookupParent groundType responseName
                        selectionSet hbodyValid
                    simpa [completeScopedSelectionSetStaticFieldsWithResponseName,
                      hallow] using
                      completeScopedSelectionSetLookupValid_append hbody hrest
              | some typeCondition =>
                  cases hbranch :
                      directivesAllowIn boolCase directives
                        && schema.typeIncludesObjectBool typeCondition
                          groundType
                  · simpa [completeScopedSelectionSetStaticFieldsWithResponseName,
                      hbranch] using hrest
                  · have hbodyValid :
                        selectionSetLookupValid schema typeCondition
                          selectionSet := by
                      simpa [selectionLookupValid] using hheadValid
                    have hbody :=
                      staticScopedFieldsWithResponseName_lookupValid schema
                        boolCase typeCondition groundType responseName
                        selectionSet hbodyValid
                    simpa [completeScopedSelectionSetStaticFieldsWithResponseName,
                      hbranch] using
                      completeScopedSelectionSetLookupValid_append hbody hrest

theorem completeScopedSelectionSetStaticFieldsWithResponseName_groundApplies
    (schema : Schema) (boolCase : BoolCase)
    (groundType responseName : Name)
    : ∀ scopedSelections,
        completeScopedSelectionSetGroundApplies schema groundType scopedSelections
        -> completeScopedSelectionSetGroundApplies schema groundType
            (completeScopedSelectionSetStaticFieldsWithResponseName schema
              boolCase groundType responseName scopedSelections)
  | [], _hground => by
      simp [completeScopedSelectionSetStaticFieldsWithResponseName,
        completeScopedSelectionSetGroundApplies]
  | scopedSelection :: rest, hground => by
      have hheadGround :
          schema.typeIncludesObjectBool scopedSelection.lookupParent
              groundType =
            true :=
        hground scopedSelection (by simp)
      have htailGround :
          completeScopedSelectionSetGroundApplies schema groundType rest := by
        intro candidate hcandidate
        exact hground candidate (by simp [hcandidate])
      have hrest :=
        completeScopedSelectionSetStaticFieldsWithResponseName_groundApplies
          schema boolCase groundType responseName rest htailGround
      cases scopedSelection with
      | mk lookupParent selection =>
          cases selection with
          | field fieldResponseName fieldName arguments directives selectionSet =>
              cases hallow :
                  directivesAllowIn boolCase directives
              · simpa [completeScopedSelectionSetStaticFieldsWithResponseName,
                  hallow] using hrest
              · cases hresponse : fieldResponseName == responseName
                · simpa [completeScopedSelectionSetStaticFieldsWithResponseName,
                    hallow, hresponse] using hrest
                · intro candidate hcandidate
                  simp [completeScopedSelectionSetStaticFieldsWithResponseName,
                    hallow, hresponse] at hcandidate
                  rcases hcandidate with hcandidate | hcandidate
                  · subst candidate
                    exact hheadGround
                  · exact hrest candidate hcandidate
          | inlineFragment typeCondition directives selectionSet =>
              cases typeCondition with
              | none =>
                  cases hallow :
                      directivesAllowIn boolCase directives
                  · simpa [completeScopedSelectionSetStaticFieldsWithResponseName,
                      hallow] using hrest
                  · have hbody :=
                      staticScopedFieldsWithResponseName_groundApplies schema
                        boolCase lookupParent groundType responseName
                        selectionSet hheadGround
                    simpa [completeScopedSelectionSetStaticFieldsWithResponseName,
                      hallow] using
                      completeScopedSelectionSetGroundApplies_append hbody hrest
              | some typeCondition =>
                  cases hbranch :
                      directivesAllowIn boolCase directives
                        && schema.typeIncludesObjectBool typeCondition
                          groundType
                  · simpa [completeScopedSelectionSetStaticFieldsWithResponseName,
                      hbranch] using hrest
                  · have htypeGround :
                        schema.typeIncludesObjectBool typeCondition
                            groundType =
                          true := by
                      cases hallow :
                          directivesAllowIn boolCase
                            directives
                      · simp [hallow] at hbranch
                      · simpa [hallow] using hbranch
                    have hbody :=
                      staticScopedFieldsWithResponseName_groundApplies schema
                        boolCase typeCondition groundType responseName
                        selectionSet htypeGround
                    simpa [completeScopedSelectionSetStaticFieldsWithResponseName,
                      hbranch] using
                      completeScopedSelectionSetGroundApplies_append hbody hrest

theorem typesOverlapBool_true_of_common_ground
    (schema : Schema) {left right groundType : Name}
    : schema.typeIncludesObjectBool left groundType = true
      -> schema.typeIncludesObjectBool right groundType = true
      -> schema.typesOverlapBool left right = true := by
  intro hleft hright
  unfold Schema.typesOverlapBool
  exact List.any_eq_true.mpr
    ⟨groundType, List.contains_iff_mem.mp hleft, hright⟩

theorem
    erase_staticScopedFieldsWithResponseName_mem_fieldSelectionsWithResponseNameInScope
    (schema : Schema) (boolCase : BoolCase) (lookupParent groundType responseName : Name)
    : ∀ selectionSet selection,
        schema.typeIncludesObjectBool lookupParent groundType = true
        -> selection
            ∈ eraseCompleteScopedSelectionSet
                (staticScopedFieldsWithResponseName schema boolCase lookupParent
                  groundType responseName selectionSet)
        -> selection
            ∈ fieldSelectionsWithResponseNameInScope schema lookupParent
                responseName selectionSet
  | [], selection, _hincludes, hmem => by
      simp [staticScopedFieldsWithResponseName,
        eraseCompleteScopedSelectionSet] at hmem
  | Selection.field fieldResponseName fieldName arguments directives
      selectionSet :: rest, selection, hincludes, hmem => by
      have hrest :=
        erase_staticScopedFieldsWithResponseName_mem_fieldSelectionsWithResponseNameInScope
          schema boolCase lookupParent groundType responseName rest
          selection hincludes
      cases hallow :
          directivesAllowIn boolCase directives
      · have hrestMem :
            selection ∈
              eraseCompleteScopedSelectionSet
                (staticScopedFieldsWithResponseName schema boolCase
                  lookupParent groundType responseName rest) := by
          simpa [staticScopedFieldsWithResponseName, hallow] using hmem
        cases hresponse : fieldResponseName == responseName <;>
          simp [fieldSelectionsWithResponseNameInScope, hresponse, hrest hrestMem]
      · cases hresponse : fieldResponseName == responseName
        · have hrestMem :
              selection ∈
                eraseCompleteScopedSelectionSet
                  (staticScopedFieldsWithResponseName schema boolCase
                    lookupParent groundType responseName rest) := by
            simpa [staticScopedFieldsWithResponseName, hallow, hresponse]
              using hmem
          simp [fieldSelectionsWithResponseNameInScope, hresponse, hrest hrestMem]
        · have hmem' :
              selection =
                  Selection.field fieldResponseName fieldName arguments
                    directives selectionSet
                ∨ selection ∈
                  eraseCompleteScopedSelectionSet
                    (staticScopedFieldsWithResponseName schema boolCase
                      lookupParent groundType responseName rest) := by
            simpa [staticScopedFieldsWithResponseName, hallow, hresponse,
              eraseCompleteScopedSelectionSet, eraseCompleteScopedSelection]
              using hmem
          rcases hmem' with hhead | htail
          · subst selection
            simp [fieldSelectionsWithResponseNameInScope, hresponse]
          · simp [fieldSelectionsWithResponseNameInScope, hresponse, hrest htail]
  | Selection.inlineFragment none directives selectionSet :: rest, selection,
      hincludes, hmem => by
      have hselection :=
        erase_staticScopedFieldsWithResponseName_mem_fieldSelectionsWithResponseNameInScope
          schema boolCase lookupParent groundType responseName selectionSet
          selection hincludes
      have hrest :=
        erase_staticScopedFieldsWithResponseName_mem_fieldSelectionsWithResponseNameInScope
          schema boolCase lookupParent groundType responseName rest
          selection hincludes
      cases hallow :
          directivesAllowIn boolCase directives
      · have hrestMem :
            selection ∈
              eraseCompleteScopedSelectionSet
                (staticScopedFieldsWithResponseName schema boolCase
                  lookupParent groundType responseName rest) := by
          simpa [staticScopedFieldsWithResponseName, hallow] using hmem
        simp [fieldSelectionsWithResponseNameInScope, hrest hrestMem]
      · have hmem' :
            selection ∈
                eraseCompleteScopedSelectionSet
                  (staticScopedFieldsWithResponseName schema boolCase
                    lookupParent groundType responseName selectionSet)
              ∨ selection ∈
                eraseCompleteScopedSelectionSet
                  (staticScopedFieldsWithResponseName schema boolCase
                    lookupParent groundType responseName rest) := by
          simpa [staticScopedFieldsWithResponseName, hallow,
            eraseCompleteScopedSelectionSet_append] using hmem
        rcases hmem' with hchild | htail
        · simp [fieldSelectionsWithResponseNameInScope, hselection hchild]
        · simp [fieldSelectionsWithResponseNameInScope, hrest htail]
  | Selection.inlineFragment (some typeCondition) directives selectionSet ::
      rest, selection, hincludes, hmem => by
      have hrest :=
        erase_staticScopedFieldsWithResponseName_mem_fieldSelectionsWithResponseNameInScope
          schema boolCase lookupParent groundType responseName rest
          selection hincludes
      cases hbranch :
          directivesAllowIn boolCase directives
            && schema.typeIncludesObjectBool typeCondition groundType
      · have hrestMem :
            selection ∈
              eraseCompleteScopedSelectionSet
                (staticScopedFieldsWithResponseName schema boolCase
                  lookupParent groundType responseName rest) := by
          simpa [staticScopedFieldsWithResponseName, hbranch] using hmem
        cases hoverlap :
            schema.typesOverlapBool lookupParent typeCondition <;>
          simp [fieldSelectionsWithResponseNameInScope, hoverlap, hrest hrestMem]
      · have hconditionIncludes :
            schema.typeIncludesObjectBool typeCondition groundType = true := by
          cases hallow :
              directivesAllowIn boolCase directives
          · simp [hallow] at hbranch
          · simpa [hallow] using hbranch
        have hoverlap :
            schema.typesOverlapBool lookupParent typeCondition = true :=
          typesOverlapBool_true_of_common_ground schema hincludes
            hconditionIncludes
        have hselection :=
          erase_staticScopedFieldsWithResponseName_mem_fieldSelectionsWithResponseNameInScope
            schema boolCase lookupParent groundType responseName
            selectionSet selection hincludes
        have hmem' :
            selection ∈
                eraseCompleteScopedSelectionSet
                  (staticScopedFieldsWithResponseName schema boolCase
                    typeCondition groundType responseName selectionSet)
              ∨ selection ∈
                eraseCompleteScopedSelectionSet
                  (staticScopedFieldsWithResponseName schema boolCase
                    lookupParent groundType responseName rest) := by
          simpa [staticScopedFieldsWithResponseName, hbranch,
            eraseCompleteScopedSelectionSet_append] using hmem
        rcases hmem' with hchild | htail
        · have hchildLookup :
              selection ∈
                eraseCompleteScopedSelectionSet
                  (staticScopedFieldsWithResponseName schema boolCase
                    lookupParent groundType responseName selectionSet) := by
            simpa [
              eraseCompleteScopedSelectionSet_staticScopedFieldsWithResponseName_lookupParent
                schema boolCase typeCondition lookupParent groundType
                responseName selectionSet] using hchild
          simp [fieldSelectionsWithResponseNameInScope, hoverlap,
            hselection hchildLookup]
        · simp [fieldSelectionsWithResponseNameInScope, hoverlap, hrest htail]

theorem staticScopedFieldsWithResponseName_mem_field
    (schema : Schema) (boolCase : BoolCase)
    (lookupParent groundType responseName : Name)
    : ∀ selectionSet scopedSelection,
        scopedSelection
          ∈ staticScopedFieldsWithResponseName schema boolCase lookupParent
              groundType responseName selectionSet
        -> ∃ fieldResponseName fieldName arguments directives subselections,
            scopedSelection.selection
            = Selection.field fieldResponseName fieldName arguments directives
                subselections
  | [], scopedSelection, hmem => by
      simp [staticScopedFieldsWithResponseName] at hmem
  | selection :: rest, scopedSelection, hmem => by
      have hrest :=
        staticScopedFieldsWithResponseName_mem_field schema boolCase
          lookupParent groundType responseName rest scopedSelection
      cases selection with
      | field fieldResponseName fieldName arguments directives selectionSet =>
          cases hallow :
              directivesAllowIn boolCase directives
          · exact hrest
              (by simpa [staticScopedFieldsWithResponseName, hallow] using hmem)
          · cases hresponse : fieldResponseName == responseName
            · exact hrest
                (by
                  simpa [staticScopedFieldsWithResponseName, hallow,
                    hresponse] using hmem)
            · have hmem' :
                  scopedSelection =
                      { lookupParent := lookupParent,
                        selection :=
                          Selection.field fieldResponseName fieldName
                            arguments directives selectionSet }
                    ∨ scopedSelection ∈
                      staticScopedFieldsWithResponseName schema boolCase
                        lookupParent groundType responseName rest := by
                  simpa [staticScopedFieldsWithResponseName, hallow, hresponse]
                    using hmem
              rcases hmem' with hhead | htail
              · subst scopedSelection
                exact ⟨fieldResponseName, fieldName, arguments, directives,
                  selectionSet, rfl⟩
              · exact hrest htail
      | inlineFragment typeCondition directives selectionSet =>
          cases typeCondition with
          | none =>
              cases hallow :
                  directivesAllowIn boolCase directives
              · exact hrest
                  (by
                    simpa [staticScopedFieldsWithResponseName, hallow]
                      using hmem)
              · have hmem' :
                    scopedSelection ∈
                        staticScopedFieldsWithResponseName schema boolCase
                          lookupParent groundType responseName selectionSet
                      ∨ scopedSelection ∈
                        staticScopedFieldsWithResponseName schema boolCase
                          lookupParent groundType responseName rest := by
                    simpa [staticScopedFieldsWithResponseName, hallow] using
                      hmem
                rcases hmem' with hchild | htail
                · exact
                    staticScopedFieldsWithResponseName_mem_field schema
                      boolCase lookupParent groundType responseName
                      selectionSet scopedSelection hchild
                · exact hrest htail
          | some typeCondition =>
              cases hbranch :
                  directivesAllowIn boolCase directives
                    && schema.typeIncludesObjectBool typeCondition groundType
              · exact hrest
                  (by
                    simpa [staticScopedFieldsWithResponseName, hbranch]
                      using hmem)
              · have hmem' :
                    scopedSelection ∈
                        staticScopedFieldsWithResponseName schema boolCase
                          typeCondition groundType responseName selectionSet
                      ∨ scopedSelection ∈
                        staticScopedFieldsWithResponseName schema boolCase
                          lookupParent groundType responseName rest := by
                    simpa [staticScopedFieldsWithResponseName, hbranch] using
                      hmem
                rcases hmem' with hchild | htail
                · exact
                    staticScopedFieldsWithResponseName_mem_field schema
                      boolCase typeCondition groundType responseName
                      selectionSet scopedSelection hchild
                · exact hrest htail

theorem collectFields_scoped_mem_lookupValid (schema : Schema) (parentType : Name)
    : ∀ selectionSet scopedField,
        selectionSetLookupValid schema parentType selectionSet
        -> scopedField ∈ FieldMerge.collectFields schema parentType selectionSet
        -> ∃ fieldDefinition,
            schema.lookupField scopedField.parentType scopedField.fieldName
              = some fieldDefinition
            ∧ fieldDefinition.outputType = scopedField.outputType
  | [], scopedField, _hlookupValid, hscoped => by
      simp [FieldMerge.collectFields] at hscoped
  | selection :: rest, scopedField, hlookupValid, hscoped => by
      have hheadLookup :
          selectionLookupValid schema parentType selection :=
        selectionSetLookupValid_head hlookupValid
      have htailLookup :
          selectionSetLookupValid schema parentType rest :=
        selectionSetLookupValid_tail hlookupValid
      cases selection with
      | field responseName fieldName arguments directives selectionSet =>
          simp [selectionLookupValid] at hheadLookup
          rcases hheadLookup with ⟨fieldDefinition, hlookup⟩
          simp [FieldMerge.collectFields, hlookup] at hscoped
          rcases hscoped with hcurrent | hrest
          · subst scopedField
            exact ⟨fieldDefinition, hlookup, rfl⟩
          · exact collectFields_scoped_mem_lookupValid schema parentType rest
              scopedField htailLookup hrest
      | inlineFragment typeCondition directives selectionSet =>
          cases typeCondition with
          | none =>
              have hselectionLookup :
                  selectionSetLookupValid schema parentType selectionSet := by
                simpa [selectionLookupValid] using hheadLookup
              simp [FieldMerge.collectFields] at hscoped
              rcases hscoped with hselectionSet | hrest
              · exact collectFields_scoped_mem_lookupValid schema parentType
                  selectionSet scopedField hselectionLookup hselectionSet
              · exact collectFields_scoped_mem_lookupValid schema parentType
                  rest scopedField htailLookup hrest
          | some typeCondition =>
              have hselectionLookup :
                  selectionSetLookupValid schema typeCondition selectionSet := by
                simpa [selectionLookupValid] using hheadLookup
              simp [FieldMerge.collectFields] at hscoped
              rcases hscoped with hselectionSet | hrest
              · exact collectFields_scoped_mem_lookupValid schema typeCondition
                  selectionSet scopedField hselectionLookup hselectionSet
              · exact collectFields_scoped_mem_lookupValid schema parentType
                  rest scopedField htailLookup hrest

theorem staticScopedFieldsWithResponseName_mem_fieldMergeCollectFields_lookupValid
    (schema : Schema) (boolCase : BoolCase) (lookupParent groundType responseName : Name)
    : ∀ selectionSet scopedSelection fieldResponseName fieldName arguments
          directives subselections,
        selectionSetLookupValid schema lookupParent selectionSet
        -> scopedSelection
            ∈ staticScopedFieldsWithResponseName schema boolCase lookupParent
                groundType responseName selectionSet
        -> scopedSelection.selection
            = Selection.field fieldResponseName fieldName arguments directives
                subselections
        -> ∃ scopedField,
            scopedField ∈ FieldMerge.collectFields schema lookupParent selectionSet
            ∧ scopedField.parentType = scopedSelection.lookupParent
            ∧ scopedField.responseName = fieldResponseName
            ∧ scopedField.fieldName = fieldName
            ∧ scopedField.arguments = arguments
            ∧ scopedField.selectionSet = subselections
  | [], scopedSelection, fieldResponseName, fieldName, arguments, directives,
      subselections, _hlookupValid, hmem, _hselection => by
      simp [staticScopedFieldsWithResponseName] at hmem
  | selection :: rest, scopedSelection, fieldResponseName, fieldName,
      arguments, directives, subselections, hlookupValid, hmem,
      hselection => by
      have hheadLookup :
          selectionLookupValid schema lookupParent selection :=
        selectionSetLookupValid_head hlookupValid
      have htailLookup :
          selectionSetLookupValid schema lookupParent rest :=
        selectionSetLookupValid_tail hlookupValid
      have hrest :=
        staticScopedFieldsWithResponseName_mem_fieldMergeCollectFields_lookupValid
          schema boolCase lookupParent groundType responseName rest
          scopedSelection fieldResponseName fieldName arguments directives
          subselections htailLookup
      cases selection with
      | field selectionResponseName selectionFieldName selectionArguments
          selectionDirectives selectionSet =>
          simp [selectionLookupValid] at hheadLookup
          rcases hheadLookup with ⟨selectionFieldDefinition, hlookup⟩
          cases hallow :
              directivesAllowIn boolCase
                selectionDirectives
          · rcases
              hrest
                (by
                  simpa [staticScopedFieldsWithResponseName, hallow] using
                    hmem)
                hselection with
              ⟨scopedField, hscoped, hparent, hresponse, hfield, hargs,
                hsubselections⟩
            refine ⟨scopedField, ?_, hparent, hresponse, hfield, hargs,
              hsubselections⟩
            simpa [FieldMerge.collectFields, hlookup] using Or.inr hscoped
          · cases hresponse : selectionResponseName == responseName
            · rcases
                hrest
                  (by
                    simpa [staticScopedFieldsWithResponseName, hallow,
                      hresponse] using hmem)
                  hselection with
                ⟨scopedField, hscoped, hresponseName, hfield, hargs,
                  hsubselections⟩
              refine ⟨scopedField, ?_, hresponseName, hfield, hargs,
                hsubselections⟩
              simpa [FieldMerge.collectFields, hlookup] using Or.inr hscoped
            · have hmem' :
                  scopedSelection =
                      { lookupParent := lookupParent,
                        selection :=
                          Selection.field selectionResponseName
                            selectionFieldName selectionArguments
                            selectionDirectives selectionSet }
                    ∨ scopedSelection ∈
                      staticScopedFieldsWithResponseName schema boolCase
                        lookupParent groundType responseName rest := by
                  simpa [staticScopedFieldsWithResponseName, hallow, hresponse]
                    using hmem
              rcases hmem' with hhead | htail
              · subst scopedSelection
                injection hselection with hresponseName hfield hargs
                  hdirectives hsubselections
                subst fieldResponseName
                subst fieldName
                subst arguments
                subst directives
                subst subselections
                refine ⟨{
                  parentType := lookupParent,
                  responseName := selectionResponseName,
                  fieldName := selectionFieldName,
                  arguments := selectionArguments,
                  outputType := selectionFieldDefinition.outputType,
                  selectionSet := selectionSet
                }, ?_, rfl, rfl, rfl, rfl, rfl⟩
                simp [FieldMerge.collectFields, hlookup]
              · rcases hrest htail hselection with
                  ⟨scopedField, hscoped, hparent, hresponseName, hfield,
                    hargs, hsubselections⟩
                refine ⟨scopedField, ?_, hparent, hresponseName, hfield,
                  hargs, hsubselections⟩
                simpa [FieldMerge.collectFields, hlookup] using Or.inr hscoped
      | inlineFragment typeCondition selectionDirectives selectionSet =>
          cases typeCondition with
          | none =>
              have hselectionLookup :
                  selectionSetLookupValid schema lookupParent selectionSet := by
                simpa [selectionLookupValid] using hheadLookup
              have hselectionRec :=
                staticScopedFieldsWithResponseName_mem_fieldMergeCollectFields_lookupValid
                  schema boolCase lookupParent groundType responseName
                  selectionSet scopedSelection fieldResponseName fieldName
                  arguments directives subselections hselectionLookup
              cases hallow :
                  directivesAllowIn boolCase
                    selectionDirectives
              · rcases
                  hrest
                    (by
                      simpa [staticScopedFieldsWithResponseName, hallow]
                        using hmem)
                    hselection with
                  ⟨scopedField, hscoped, hparent, hresponseName, hfield,
                    hargs, hsubselections⟩
                refine ⟨scopedField, ?_, hparent, hresponseName, hfield,
                  hargs, hsubselections⟩
                simp [FieldMerge.collectFields, hscoped]
              · have hmem' :
                    scopedSelection ∈
                        staticScopedFieldsWithResponseName schema boolCase
                          lookupParent groundType responseName selectionSet
                      ∨ scopedSelection ∈
                        staticScopedFieldsWithResponseName schema boolCase
                          lookupParent groundType responseName rest := by
                    simpa [staticScopedFieldsWithResponseName, hallow] using
                      hmem
                rcases hmem' with hchild | htail
                · rcases hselectionRec hchild hselection with
                    ⟨scopedField, hscoped, hparent, hresponseName, hfield,
                      hargs, hsubselections⟩
                  refine ⟨scopedField, ?_, hparent, hresponseName, hfield,
                    hargs, hsubselections⟩
                  simp [FieldMerge.collectFields, hscoped]
                · rcases hrest htail hselection with
                    ⟨scopedField, hscoped, hparent, hresponseName, hfield,
                      hargs, hsubselections⟩
                  refine ⟨scopedField, ?_, hparent, hresponseName, hfield,
                    hargs, hsubselections⟩
                  simp [FieldMerge.collectFields, hscoped]
          | some typeCondition =>
              have hselectionLookup :
                  selectionSetLookupValid schema typeCondition selectionSet := by
                simpa [selectionLookupValid] using hheadLookup
              have hselectionRec :=
                staticScopedFieldsWithResponseName_mem_fieldMergeCollectFields_lookupValid
                  schema boolCase typeCondition groundType responseName
                  selectionSet scopedSelection fieldResponseName fieldName
                  arguments directives subselections hselectionLookup
              cases hbranch :
                  directivesAllowIn boolCase
                      selectionDirectives
                    && schema.typeIncludesObjectBool typeCondition groundType
              · rcases
                  hrest
                    (by
                      simpa [staticScopedFieldsWithResponseName, hbranch]
                        using hmem)
                    hselection with
                  ⟨scopedField, hscoped, hparent, hresponseName, hfield,
                    hargs, hsubselections⟩
                refine ⟨scopedField, ?_, hparent, hresponseName, hfield,
                  hargs, hsubselections⟩
                simp [FieldMerge.collectFields, hscoped]
              · have hmem' :
                    scopedSelection ∈
                        staticScopedFieldsWithResponseName schema boolCase
                          typeCondition groundType responseName selectionSet
                      ∨ scopedSelection ∈
                        staticScopedFieldsWithResponseName schema boolCase
                          lookupParent groundType responseName rest := by
                    simpa [staticScopedFieldsWithResponseName, hbranch] using
                      hmem
                rcases hmem' with hchild | htail
                · rcases hselectionRec hchild hselection with
                    ⟨scopedField, hscoped, hparent, hresponseName, hfield,
                      hargs, hsubselections⟩
                  refine ⟨scopedField, ?_, hparent, hresponseName, hfield,
                    hargs, hsubselections⟩
                  simp [FieldMerge.collectFields, hscoped]
                · rcases hrest htail hselection with
                    ⟨scopedField, hscoped, hparent, hresponseName, hfield,
                      hargs, hsubselections⟩
                  refine ⟨scopedField, ?_, hparent, hresponseName, hfield,
                    hargs, hsubselections⟩
                  simp [FieldMerge.collectFields, hscoped]

theorem staticScopedFieldsWithResponseName_mem_fieldMergeCollectFields
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (boolCase : BoolCase)
    (lookupParent groundType responseName : Name)
    : ∀ selectionSet scopedSelection fieldResponseName fieldName arguments
          directives subselections,
        Validation.selectionSetValid schema variableDefinitions lookupParent selectionSet
        -> scopedSelection
            ∈ staticScopedFieldsWithResponseName schema boolCase lookupParent
                groundType responseName selectionSet
        -> scopedSelection.selection
            = Selection.field fieldResponseName fieldName arguments directives
                subselections
        -> ∃ scopedField,
            scopedField ∈ FieldMerge.collectFields schema lookupParent selectionSet
            ∧ scopedField.parentType = scopedSelection.lookupParent
            ∧ scopedField.responseName = fieldResponseName
            ∧ scopedField.fieldName = fieldName
            ∧ scopedField.arguments = arguments
            ∧ scopedField.selectionSet = subselections
  | [], scopedSelection, fieldResponseName, fieldName, arguments, directives,
      subselections, _hvalid, hmem, _hselection => by
      simp [staticScopedFieldsWithResponseName] at hmem
  | selection :: rest, scopedSelection, fieldResponseName, fieldName,
      arguments, directives, subselections, hvalid, hmem, hselection => by
      have hheadValid :
          Validation.selectionValid schema variableDefinitions lookupParent
            selection := by
        simp [Validation.selectionSetValid] at hvalid
        exact hvalid.1
      have htailValid :
          Validation.selectionSetValid schema variableDefinitions lookupParent
            rest :=
        Validation.selectionSetValid_tail hvalid
      have hrest :=
        staticScopedFieldsWithResponseName_mem_fieldMergeCollectFields
          schema variableDefinitions boolCase lookupParent groundType
          responseName rest scopedSelection fieldResponseName fieldName
          arguments directives subselections htailValid
      cases selection with
      | field selectionResponseName selectionFieldName selectionArguments
          selectionDirectives selectionSet =>
          rcases Validation.selectionValid_field_lookup hheadValid with
            ⟨selectionFieldDefinition, hlookup, _harguments, _hchild⟩
          cases hallow :
              directivesAllowIn boolCase
                selectionDirectives
          · rcases
              hrest
                (by
                  simpa [staticScopedFieldsWithResponseName, hallow] using
                    hmem)
                hselection with
              ⟨scopedField, hscoped, hparent, hresponse, hfield, hargs,
                hsubselections⟩
            refine ⟨scopedField, ?_, hparent, hresponse, hfield, hargs,
              hsubselections⟩
            simpa [FieldMerge.collectFields, hlookup] using Or.inr hscoped
          · cases hresponse : selectionResponseName == responseName
            · rcases
                hrest
                  (by
                    simpa [staticScopedFieldsWithResponseName, hallow,
                      hresponse] using hmem)
                  hselection with
                ⟨scopedField, hscoped, hparent, hresponseName, hfield, hargs,
                  hsubselections⟩
              refine ⟨scopedField, ?_, hparent, hresponseName, hfield, hargs,
                hsubselections⟩
              simpa [FieldMerge.collectFields, hlookup] using Or.inr hscoped
            · have hmem' :
                  scopedSelection =
                      { lookupParent := lookupParent,
                        selection :=
                          Selection.field selectionResponseName
                            selectionFieldName selectionArguments
                            selectionDirectives selectionSet }
                    ∨ scopedSelection ∈
                      staticScopedFieldsWithResponseName schema boolCase
                        lookupParent groundType responseName rest := by
                  simpa [staticScopedFieldsWithResponseName, hallow, hresponse]
                    using hmem
              rcases hmem' with hhead | htail
              · subst scopedSelection
                injection hselection with hresponseName hfield hargs
                  hdirectives hsubselections
                subst fieldResponseName
                subst fieldName
                subst arguments
                subst directives
                subst subselections
                refine ⟨{
                  parentType := lookupParent,
                  responseName := selectionResponseName,
                  fieldName := selectionFieldName,
                  arguments := selectionArguments,
                  outputType := selectionFieldDefinition.outputType,
                  selectionSet := selectionSet
                }, ?_, rfl, rfl, rfl, rfl, rfl⟩
                simp [FieldMerge.collectFields, hlookup]
              · rcases hrest htail hselection with
                  ⟨scopedField, hscoped, hparent, hresponseName, hfield,
                    hargs, hsubselections⟩
                refine ⟨scopedField, ?_, hparent, hresponseName, hfield,
                  hargs, hsubselections⟩
                simpa [FieldMerge.collectFields, hlookup] using Or.inr hscoped
      | inlineFragment typeCondition selectionDirectives selectionSet =>
          cases typeCondition with
          | none =>
              have hselectionValid :
                  Validation.selectionSetValid schema variableDefinitions
                    lookupParent selectionSet :=
                Validation.selectionValid_inlineFragment_none_selectionSetValid
                  hheadValid
              have hselectionRec :=
                staticScopedFieldsWithResponseName_mem_fieldMergeCollectFields
                  schema variableDefinitions boolCase lookupParent groundType
                  responseName selectionSet scopedSelection fieldResponseName
                  fieldName arguments directives subselections hselectionValid
              cases hallow :
                  directivesAllowIn boolCase
                    selectionDirectives
              · rcases
                  hrest
                    (by
                      simpa [staticScopedFieldsWithResponseName, hallow]
                        using hmem)
                    hselection with
                  ⟨scopedField, hscoped, hparent, hresponseName, hfield,
                    hargs, hsubselections⟩
                refine ⟨scopedField, ?_, hparent, hresponseName, hfield,
                  hargs, hsubselections⟩
                simp [FieldMerge.collectFields, hscoped]
              · have hmem' :
                    scopedSelection ∈
                        staticScopedFieldsWithResponseName schema boolCase
                          lookupParent groundType responseName selectionSet
                      ∨ scopedSelection ∈
                        staticScopedFieldsWithResponseName schema boolCase
                          lookupParent groundType responseName rest := by
                    simpa [staticScopedFieldsWithResponseName, hallow] using
                      hmem
                rcases hmem' with hchild | htail
                · rcases hselectionRec hchild hselection with
                    ⟨scopedField, hscoped, hparent, hresponseName, hfield,
                      hargs, hsubselections⟩
                  refine ⟨scopedField, ?_, hparent, hresponseName, hfield,
                    hargs, hsubselections⟩
                  simp [FieldMerge.collectFields, hscoped]
                · rcases hrest htail hselection with
                    ⟨scopedField, hscoped, hparent, hresponseName, hfield,
                      hargs, hsubselections⟩
                  refine ⟨scopedField, ?_, hparent, hresponseName, hfield,
                    hargs, hsubselections⟩
                  simp [FieldMerge.collectFields, hscoped]
          | some typeCondition =>
              have hselectionValid :
                  Validation.selectionSetValid schema variableDefinitions
                    typeCondition selectionSet :=
                Validation.selectionValid_inlineFragment_some_selectionSetValid
                  hheadValid
              have hselectionRec :=
                staticScopedFieldsWithResponseName_mem_fieldMergeCollectFields
                  schema variableDefinitions boolCase typeCondition
                  groundType responseName selectionSet scopedSelection
                  fieldResponseName fieldName arguments directives subselections
                  hselectionValid
              cases hbranch :
                  directivesAllowIn boolCase
                      selectionDirectives
                    && schema.typeIncludesObjectBool typeCondition groundType
              · rcases
                  hrest
                    (by
                      simpa [staticScopedFieldsWithResponseName, hbranch]
                        using hmem)
                    hselection with
                  ⟨scopedField, hscoped, hparent, hresponseName, hfield,
                    hargs, hsubselections⟩
                refine ⟨scopedField, ?_, hparent, hresponseName, hfield,
                  hargs, hsubselections⟩
                simp [FieldMerge.collectFields, hscoped]
              · have hmem' :
                    scopedSelection ∈
                        staticScopedFieldsWithResponseName schema boolCase
                          typeCondition groundType responseName selectionSet
                      ∨ scopedSelection ∈
                        staticScopedFieldsWithResponseName schema boolCase
                          lookupParent groundType responseName rest := by
                    simpa [staticScopedFieldsWithResponseName, hbranch] using
                      hmem
                rcases hmem' with hchild | htail
                · rcases hselectionRec hchild hselection with
                    ⟨scopedField, hscoped, hparent, hresponseName, hfield,
                      hargs, hsubselections⟩
                  refine ⟨scopedField, ?_, hparent, hresponseName, hfield,
                    hargs, hsubselections⟩
                  simp [FieldMerge.collectFields, hscoped]
                · rcases hrest htail hselection with
                    ⟨scopedField, hscoped, hparent, hresponseName, hfield,
                      hargs, hsubselections⟩
                  refine ⟨scopedField, ?_, hparent, hresponseName, hfield,
                    hargs, hsubselections⟩
                  simp [FieldMerge.collectFields, hscoped]

theorem staticScopedFieldsWithResponseName_mem_field_allowed
    (schema : Schema) (boolCase : BoolCase)
    (lookupParent groundType responseName : Name)
    : ∀ selectionSet scopedSelection fieldResponseName fieldName arguments
          directives subselections,
        scopedSelection
          ∈ staticScopedFieldsWithResponseName schema boolCase lookupParent
              groundType responseName selectionSet
        -> scopedSelection.selection
            = Selection.field fieldResponseName fieldName arguments directives
                subselections
        -> directivesAllowIn boolCase directives = true
  | [], scopedSelection, fieldResponseName, fieldName, arguments, directives,
      subselections, hmem, _hselection => by
      simp [staticScopedFieldsWithResponseName] at hmem
  | selection :: rest, scopedSelection, fieldResponseName, fieldName,
      arguments, directives, subselections, hmem, hselection => by
      have hrest :=
        staticScopedFieldsWithResponseName_mem_field_allowed schema boolCase
          lookupParent groundType responseName rest scopedSelection
          fieldResponseName fieldName arguments directives subselections
      cases selection with
      | field selectionResponseName selectionFieldName selectionArguments
          selectionDirectives selectionSet =>
          cases hallow :
              directivesAllowIn boolCase
                selectionDirectives
          · exact hrest
              (by simpa [staticScopedFieldsWithResponseName, hallow] using hmem)
              hselection
          · cases hresponse : selectionResponseName == responseName
            · exact hrest
                (by
                  simpa [staticScopedFieldsWithResponseName, hallow,
                    hresponse] using hmem)
                hselection
            · have hmem' :
                  scopedSelection =
                      { lookupParent := lookupParent,
                        selection :=
                          Selection.field selectionResponseName
                            selectionFieldName selectionArguments
                            selectionDirectives selectionSet }
                    ∨ scopedSelection ∈
                      staticScopedFieldsWithResponseName schema boolCase
                        lookupParent groundType responseName rest := by
                  simpa [staticScopedFieldsWithResponseName, hallow, hresponse]
                    using hmem
              rcases hmem' with hhead | htail
              · subst scopedSelection
                injection hselection with _hresponse _hfield _harguments
                  hdirectives _hsubselections
                subst directives
                exact hallow
              · exact hrest htail hselection
      | inlineFragment typeCondition selectionDirectives selectionSet =>
          cases typeCondition with
          | none =>
              cases hallow :
                  directivesAllowIn boolCase
                    selectionDirectives
              · exact hrest
                  (by
                    simpa [staticScopedFieldsWithResponseName, hallow]
                      using hmem)
                  hselection
              · have hmem' :
                    scopedSelection ∈
                        staticScopedFieldsWithResponseName schema boolCase
                          lookupParent groundType responseName selectionSet
                      ∨ scopedSelection ∈
                        staticScopedFieldsWithResponseName schema boolCase
                          lookupParent groundType responseName rest := by
                    simpa [staticScopedFieldsWithResponseName, hallow] using
                      hmem
                rcases hmem' with hchild | htail
                · exact
                    staticScopedFieldsWithResponseName_mem_field_allowed
                      schema boolCase lookupParent groundType responseName
                      selectionSet scopedSelection fieldResponseName fieldName
                      arguments directives subselections hchild hselection
                · exact hrest htail hselection
          | some typeCondition =>
              cases hbranch :
                  directivesAllowIn boolCase
                      selectionDirectives
                    && schema.typeIncludesObjectBool typeCondition groundType
              · exact hrest
                  (by
                    simpa [staticScopedFieldsWithResponseName, hbranch]
                      using hmem)
                  hselection
              · have hmem' :
                    scopedSelection ∈
                        staticScopedFieldsWithResponseName schema boolCase
                          typeCondition groundType responseName selectionSet
                      ∨ scopedSelection ∈
                        staticScopedFieldsWithResponseName schema boolCase
                          lookupParent groundType responseName rest := by
                    simpa [staticScopedFieldsWithResponseName, hbranch] using
                      hmem
                rcases hmem' with hchild | htail
                · exact
                    staticScopedFieldsWithResponseName_mem_field_allowed
                      schema boolCase typeCondition groundType responseName
                      selectionSet scopedSelection fieldResponseName fieldName
                      arguments directives subselections hchild hselection
                · exact hrest htail hselection

theorem completeScopedSelectionSetStaticFieldsWithResponseName_mem_field_allowed
    (schema : Schema) (boolCase : BoolCase)
    (groundType responseName : Name)
    : ∀ scopedSelections scopedSelection fieldResponseName fieldName arguments
          directives subselections,
        scopedSelection
          ∈ completeScopedSelectionSetStaticFieldsWithResponseName schema
              boolCase groundType responseName scopedSelections
        -> scopedSelection.selection
            = Selection.field fieldResponseName fieldName arguments directives
                subselections
        -> directivesAllowIn boolCase directives = true
  | [], scopedSelection, fieldResponseName, fieldName, arguments, directives,
      subselections, hmem, _hselection => by
      simp [completeScopedSelectionSetStaticFieldsWithResponseName] at hmem
  | head :: rest, scopedSelection, fieldResponseName, fieldName, arguments,
      directives, subselections, hmem, hselection => by
      have hrest :=
        completeScopedSelectionSetStaticFieldsWithResponseName_mem_field_allowed
          schema boolCase groundType responseName rest scopedSelection
          fieldResponseName fieldName arguments directives subselections
      cases head with
      | mk lookupParent selection =>
          cases selection with
          | field selectionResponseName selectionFieldName selectionArguments
              selectionDirectives selectionSet =>
              cases hallow :
                  directivesAllowIn boolCase
                    selectionDirectives
              · exact hrest
                  (by
                    simpa [
                      completeScopedSelectionSetStaticFieldsWithResponseName,
                      hallow] using hmem)
                  hselection
              · cases hresponse : selectionResponseName == responseName
                · exact hrest
                    (by
                      simpa [
                        completeScopedSelectionSetStaticFieldsWithResponseName,
                        hallow, hresponse] using hmem)
                    hselection
                · have hmem' :
                      scopedSelection =
                          { lookupParent := lookupParent,
                            selection :=
                              Selection.field selectionResponseName
                                selectionFieldName selectionArguments
                                selectionDirectives selectionSet }
                        ∨ scopedSelection ∈
                          completeScopedSelectionSetStaticFieldsWithResponseName
                            schema boolCase groundType responseName rest := by
                      simpa [
                        completeScopedSelectionSetStaticFieldsWithResponseName,
                        hallow, hresponse] using hmem
                  rcases hmem' with hhead | htail
                  · subst scopedSelection
                    injection hselection with _hresponse _hfield _harguments
                      hdirectives _hsubselections
                    subst directives
                    exact hallow
                  · exact hrest htail hselection
          | inlineFragment typeCondition selectionDirectives selectionSet =>
              cases typeCondition with
              | none =>
                  cases hallow :
                      directivesAllowIn boolCase
                        selectionDirectives
                  · exact hrest
                      (by
                        simpa [
                          completeScopedSelectionSetStaticFieldsWithResponseName,
                          hallow] using hmem)
                      hselection
                  · have hmem' :
                        scopedSelection ∈
                            staticScopedFieldsWithResponseName schema
                              boolCase lookupParent groundType responseName
                              selectionSet
                          ∨ scopedSelection ∈
                            completeScopedSelectionSetStaticFieldsWithResponseName
                              schema boolCase groundType responseName rest := by
                        simpa [
                          completeScopedSelectionSetStaticFieldsWithResponseName,
                          hallow] using hmem
                    rcases hmem' with hchild | htail
                    · exact
                        staticScopedFieldsWithResponseName_mem_field_allowed
                          schema boolCase lookupParent groundType
                          responseName selectionSet scopedSelection
                          fieldResponseName fieldName arguments directives
                          subselections hchild hselection
                    · exact hrest htail hselection
              | some typeCondition =>
                  cases hbranch :
                      directivesAllowIn boolCase
                          selectionDirectives
                        && schema.typeIncludesObjectBool typeCondition
                          groundType
                  · exact hrest
                      (by
                        simpa [
                          completeScopedSelectionSetStaticFieldsWithResponseName,
                          hbranch] using hmem)
                      hselection
                  · have hmem' :
                        scopedSelection ∈
                            staticScopedFieldsWithResponseName schema
                              boolCase typeCondition groundType responseName
                              selectionSet
                          ∨ scopedSelection ∈
                            completeScopedSelectionSetStaticFieldsWithResponseName
                              schema boolCase groundType responseName rest := by
                        simpa [
                          completeScopedSelectionSetStaticFieldsWithResponseName,
                          hbranch] using hmem
                    rcases hmem' with hchild | htail
                    · exact
                        staticScopedFieldsWithResponseName_mem_field_allowed
                          schema boolCase typeCondition groundType
                          responseName selectionSet scopedSelection
                          fieldResponseName fieldName arguments directives
                          subselections hchild hselection
                    · exact hrest htail hselection

end CompleteNormalization

end NormalForm

end GraphQL
