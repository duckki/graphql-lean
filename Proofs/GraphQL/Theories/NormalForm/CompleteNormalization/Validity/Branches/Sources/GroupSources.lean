import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Validity.Branches.FieldMerge

/-!
Normalized group-source collection facts for complete-normalization branch validity.
-/

namespace GraphQL

namespace NormalForm

namespace CompleteNormalization

open GroundTypeNormalization

structure BoolFilteredScopedFieldSource
    (schema : Schema) (boolCase : BoolCase)
    (source filtered : FieldMerge.ScopedField)
    : Prop where
  parentType : filtered.parentType = source.parentType
  responseName : filtered.responseName = source.responseName
  fieldName : filtered.fieldName = source.fieldName
  arguments : filtered.arguments = source.arguments
  outputType : filtered.outputType = source.outputType
  selectionSet
    : filtered.selectionSet = filterSelectionSetBoolCase boolCase source.selectionSet

theorem normalizedFieldSource_of_boolFiltered
    {schema : Schema} {boolCase : BoolCase}
    {source filtered normalized : FieldMerge.ScopedField}
    : BoolFilteredScopedFieldSource schema boolCase source filtered
      -> GroundTypeNormalization.NormalizedFieldSource schema filtered normalized
      -> GroundTypeNormalization.NormalizedFieldSource schema source normalized := by
  intro hfiltered hnormalized
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact hfiltered.responseName.symm.trans hnormalized.responseName
  · exact hfiltered.fieldName.symm.trans hnormalized.fieldName
  · exact hfiltered.arguments.symm.trans hnormalized.arguments
  · simpa [← hfiltered.outputType] using hnormalized.outputShape
  · rcases hnormalized.parentCondition with hparent | hnotObject
    · exact Or.inl (hfiltered.parentType.symm.trans hparent)
    · exact Or.inr (by
        intro hsourceObject
        exact hnotObject (by
          simpa [hfiltered.parentType] using hsourceObject))

private theorem selectionSet_size_append_for_completeValidity
    (left right : List Selection)
    : SelectionSet.size (left ++ right)
      = SelectionSet.size left + SelectionSet.size right := by
  induction left with
  | nil => simp [SelectionSet.size]
  | cons selection rest ih =>
      simp [SelectionSet.size, ih, Nat.add_assoc]

private theorem mergeSelectionSets_append_for_completeValidity
    (left right : List Selection)
    : mergeSelectionSets (left ++ right)
      = mergeSelectionSets left ++ mergeSelectionSets right := by
  induction left with
  | nil =>
      simp [mergeSelectionSets]
  | cons selection rest ih =>
      simp [mergeSelectionSets, ih, List.append_assoc]

private theorem selectionSet_size_tail_lt_cons_for_completeValidity
    (selection : Selection) (rest : List Selection)
    : SelectionSet.size rest < SelectionSet.size (selection :: rest) := by
  cases selection <;> simp [SelectionSet.size, Selection.size] <;> omega

private theorem size_withoutFieldSelectionsWithResponseName_le_for_completeValidity
    (schema : Schema) (responseName : Name)
    : ∀ selectionSet,
        SelectionSet.size
          (withoutFieldSelectionsWithResponseName schema responseName selectionSet)
        ≤ SelectionSet.size selectionSet
  | [] => by
      simp [withoutFieldSelectionsWithResponseName, SelectionSet.size]
  | selection :: rest => by
      cases selection with
      | field fieldResponseName fieldName arguments directives selectionSet =>
          have hrest :=
            size_withoutFieldSelectionsWithResponseName_le_for_completeValidity
              schema responseName rest
          by_cases h : (fieldResponseName == responseName) = true
          · simp [withoutFieldSelectionsWithResponseName, h, SelectionSet.size,
              Selection.size]
            omega
          · have hfalse : (fieldResponseName == responseName) = false := by
              cases hmatch : fieldResponseName == responseName
              · rfl
              · contradiction
            simp [withoutFieldSelectionsWithResponseName, hfalse, SelectionSet.size,
              Selection.size]
            omega
      | inlineFragment typeCondition directives selectionSet =>
          have hselectionSet :=
            size_withoutFieldSelectionsWithResponseName_le_for_completeValidity
              schema responseName selectionSet
          have hrest :=
            size_withoutFieldSelectionsWithResponseName_le_for_completeValidity
              schema responseName rest
          cases typeCondition <;>
            simp [withoutFieldSelectionsWithResponseName, SelectionSet.size,
              Selection.size]
          all_goals omega
termination_by selectionSet => SelectionSet.size selectionSet
decreasing_by
  all_goals
    simp [SelectionSet.size, Selection.size]
    omega

private theorem
    size_mergeSelectionSets_fieldSelectionsWithResponseNameInScope_le_for_completeValidity
    (schema : Schema) (parentType responseName : Name)
    : ∀ selectionSet,
        SelectionSet.size
          (mergeSelectionSets
            (fieldSelectionsWithResponseNameInScope schema parentType responseName
              selectionSet))
        ≤ SelectionSet.size selectionSet
  | [] => by
      simp [fieldSelectionsWithResponseNameInScope, mergeSelectionSets,
        SelectionSet.size]
  | selection :: rest => by
      cases selection with
      | field fieldResponseName fieldName arguments directives selectionSet =>
          have hrest :=
            size_mergeSelectionSets_fieldSelectionsWithResponseNameInScope_le_for_completeValidity
              schema parentType responseName rest
          by_cases h : (fieldResponseName == responseName) = true
          · simp [fieldSelectionsWithResponseNameInScope, mergeSelectionSets, h,
              selectionSet_size_append_for_completeValidity,
              SelectionSet.size, Selection.size, Selection.subselections]
            omega
          · have hfalse : (fieldResponseName == responseName) = false := by
              cases hmatch : fieldResponseName == responseName
              · rfl
              · contradiction
            simp [fieldSelectionsWithResponseNameInScope, hfalse, SelectionSet.size,
              Selection.size]
            omega
      | inlineFragment typeCondition directives selectionSet =>
          have hselectionSet :=
            size_mergeSelectionSets_fieldSelectionsWithResponseNameInScope_le_for_completeValidity
              schema parentType responseName selectionSet
          have hrest :=
            size_mergeSelectionSets_fieldSelectionsWithResponseNameInScope_le_for_completeValidity
              schema parentType responseName rest
          cases typeCondition with
          | none =>
              simp [fieldSelectionsWithResponseNameInScope,
                mergeSelectionSets_append_for_completeValidity,
                selectionSet_size_append_for_completeValidity,
                SelectionSet.size, Selection.size]
              omega
          | some typeCondition =>
              by_cases h :
                  schema.typesOverlapBool parentType typeCondition = true
              · simp [fieldSelectionsWithResponseNameInScope, h,
                  mergeSelectionSets_append_for_completeValidity,
                  selectionSet_size_append_for_completeValidity,
                  SelectionSet.size, Selection.size]
                omega
              · have hfalse :
                    schema.typesOverlapBool parentType typeCondition = false := by
                  cases hmatch : schema.typesOverlapBool parentType typeCondition
                  · rfl
                  · contradiction
                simp [fieldSelectionsWithResponseNameInScope, hfalse,
                  SelectionSet.size, Selection.size]
                omega
termination_by selectionSet => SelectionSet.size selectionSet
decreasing_by
  all_goals
    simp [SelectionSet.size, Selection.size]
    omega

structure NormalizedFieldGroupSource
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType : Name) (selectionSet : List Selection)
    (normalized : FieldMerge.ScopedField) where
  source : FieldMerge.ScopedField
  sourceMem : source ∈ FieldMerge.collectFields schema parentType selectionSet
  sourceRel : GroundTypeNormalization.NormalizedFieldSource schema source normalized
  group : List Selection
  childSource : List Selection
  childSource_eq : childSource = mergeSelectionSets group
  childSource_size_lt : SelectionSet.size childSource < SelectionSet.size selectionSet
  childReady
    : ∀ runtimeType,
        runtimeType ∈ schema.getPossibleTypes normalized.outputType.namedType
        -> selectionSetSemanticsReady schema runtimeType childSource
  childLookup : selectionSetLookupValid schema normalized.outputType.namedType childSource
  childImplementation
    : ∀ runtimeType,
        runtimeType ∈ schema.getPossibleTypes normalized.outputType.namedType
        -> Validation.selectionSetValidInPossibleTypes schema
            variableDefinitions runtimeType childSource
  childFeasible
    : ∀ runtimeType,
        runtimeType ∈ schema.getPossibleTypes normalized.outputType.namedType
        -> selectionSetTypeConditionFeasible schema runtimeType [runtimeType] childSource
  childDirectiveFree : selectionSetDirectiveFree childSource
  groupScoped
    : ∀ selection,
        selection ∈ group
        -> ∃ scopedField,
            scopedField ∈ FieldMerge.collectFields schema parentType selectionSet
            ∧ scopedField.responseName = normalized.responseName
            ∧ scopedField.selectionSet = selection.subselections
            ∧ (schema.objectType scopedField.parentType
                -> schema.typesOverlapBool parentType scopedField.parentType = true)
  normalizedSelectionSet
    : normalized.selectionSet
      = if objectTypeNameBool schema normalized.outputType.namedType then
          normalizeSelectionSet schema normalized.outputType.namedType childSource
        else
          GroundTypeNormalization.possibleTypeNormalizations schema
            (schema.getPossibleTypes normalized.outputType.namedType)
            childSource

def normalizedFieldGroupSource_fieldHead
    (schema : Schema)
    (variableDefinitions : List VariableDefinition)
    (parentType responseName fieldName : Name)
    (arguments : List Argument) (directives : List DirectiveApplication)
    (subselections rest : List Selection)
    (fieldDefinition : FieldDefinition)
    : SchemaWellFormedness.schemaWellFormed schema -> schema.objectType parentType
      -> selectionSetSemanticsReady schema parentType
          (Selection.field responseName fieldName arguments directives subselections
            :: rest)
      -> selectionSetLookupValid schema parentType rest
      -> selectionSetLookupValid schema parentType
          (Selection.field responseName fieldName arguments directives subselections
            :: rest)
      -> Validation.selectionSetValidInPossibleTypes schema
          variableDefinitions parentType
          (Selection.field responseName fieldName arguments directives subselections
            :: rest)
      -> FieldMerge.fieldsInSetCanMerge schema parentType
          (Selection.field responseName fieldName arguments directives subselections
            :: rest)
      -> selectionSetDirectiveFree
          (Selection.field responseName fieldName arguments directives subselections
            :: rest)
      -> objectSatisfiesTypeConditionStack schema parentType typeConditions
      -> selectionSetTypeConditionFeasible schema parentType typeConditions

          (Selection.field responseName fieldName arguments directives subselections
            :: rest)
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> NormalizedFieldGroupSource schema variableDefinitions parentType
          (Selection.field responseName fieldName arguments directives subselections
            :: rest)
          {
            parentType := parentType,
            responseName := responseName,
            fieldName := fieldName,
            arguments := arguments,
            outputType := fieldDefinition.outputType,
            selectionSet :=
              if objectTypeNameBool schema fieldDefinition.outputType.namedType then
                normalizeSelectionSet schema fieldDefinition.outputType.namedType
                  (subselections
                    ++ mergeSelectionSets
                        (fieldSelectionsWithResponseNameInScope schema parentType
                          responseName rest))
              else
                GroundTypeNormalization.possibleTypeNormalizations schema
                  (schema.getPossibleTypes fieldDefinition.outputType.namedType)
                  (subselections
                    ++ mergeSelectionSets
                        (fieldSelectionsWithResponseNameInScope schema parentType
                          responseName rest))
          } := by
  intro hschema hobject hready htailLookup hlookupValid himplementation
    hmerge hfree hstack hfeasible hlookup
  have hselectionFree := selectionSetDirectiveFree_head hfree
  have hdirectives : directives = [] := hselectionFree.1
  subst directives
  let headSelection : Selection :=
    Selection.field responseName fieldName arguments [] subselections
  let group : List Selection :=
    headSelection :: fieldSelectionsWithResponseNameInScope schema parentType
      responseName rest
  let childSource : List Selection := mergeSelectionSets group
  let sourceField : FieldMerge.ScopedField := {
    parentType := parentType,
    responseName := responseName,
    fieldName := fieldName,
    arguments := arguments,
    outputType := fieldDefinition.outputType,
    selectionSet := subselections
  }
  refine ⟨sourceField, ?_, ?_, group, childSource, rfl, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · simp [sourceField, FieldMerge.collectFields, hlookup]
  · refine ⟨rfl, rfl, rfl, ?_, Or.inl rfl⟩
    exact FieldMerge.sameResponseShape_refl schema
      fieldDefinition.outputType
      (SchemaWellFormedness.schemaWellFormed_lookupField_outputType
        hschema hlookup)
  · have hmatchingSize :
        SelectionSet.size
            (mergeSelectionSets
              (fieldSelectionsWithResponseNameInScope schema parentType responseName
                rest))
          ≤ SelectionSet.size rest :=
      size_mergeSelectionSets_fieldSelectionsWithResponseNameInScope_le_for_completeValidity
        schema parentType responseName rest
    simp [childSource, group, headSelection, mergeSelectionSets,
      Selection.subselections, selectionSet_size_append_for_completeValidity,
      SelectionSet.size, Selection.size]
    omega
  · intro runtimeType hpossible
    have hinclude :
        schema.typeIncludesObjectBool fieldDefinition.outputType.namedType
          runtimeType = true :=
      List.contains_iff_mem.mpr hpossible
    simpa [childSource, group, headSelection, mergeSelectionSets,
      Selection.subselections] using
      selectionSetSemanticsReady_fieldHead_merged_of_child_object
        schema parentType responseName fieldName runtimeType arguments
        subselections rest fieldDefinition hobject hready hlookupValid hmerge
        hlookup hinclude
  · simpa [childSource, group, headSelection, mergeSelectionSets,
      Selection.subselections] using
      GroundTypeNormalization.selectionSetLookupValid_fieldHead_merged_of_returnType
        schema variableDefinitions parentType responseName fieldName
        arguments subselections rest fieldDefinition hobject hlookupValid
        himplementation hmerge hlookup
  · intro runtimeType hpossible
    have hinclude :
        schema.typeIncludesObjectBool fieldDefinition.outputType.namedType
          runtimeType = true :=
      List.contains_iff_mem.mpr hpossible
    simpa [childSource, group, headSelection, mergeSelectionSets,
      Selection.subselections] using
      GroundTypeNormalization.selectionSetValidInPossibleTypes_fieldHead_merged_of_child_object
        schema variableDefinitions parentType responseName fieldName
        runtimeType arguments subselections rest fieldDefinition hobject
        hlookupValid himplementation hmerge hlookup hinclude
  · intro runtimeType hpossible
    have hheadFeasible :
        selectionTypeConditionFeasible schema parentType typeConditions

          (Selection.field responseName fieldName arguments [] subselections) := by
      simpa [selectionSetTypeConditionFeasible] using hfeasible.1
    have htailFeasible :
        selectionSetTypeConditionFeasible schema parentType typeConditions
           rest :=
      selectionSetTypeConditionFeasible_tail hfeasible
    have hheadChildFeasible :
        selectionSetTypeConditionFeasible schema runtimeType [runtimeType]

          subselections :=
      selectionTypeConditionFeasible_field_child_branch_forObject
        schema hheadFeasible hstack hlookup hpossible
    have hmatchingChildFeasible :
        selectionSetTypeConditionFeasible schema runtimeType [runtimeType]

          (mergeSelectionSets
            (fieldSelectionsWithResponseNameInScope schema parentType responseName
              rest)) := by
      apply
        selectionSetTypeConditionFeasible_mergeSelectionSets_fieldSelectionsWithResponseNameInScope
      intro matchedFieldName matchedArguments matchedDirectives
        matchedSubselections hmatched
      have hsame :
          matchedFieldName = fieldName :=
        fieldSelectionsWithResponseNameInScope_matching_same_field_of_canMerge_object_lookupValid
          schema parentType responseName fieldName arguments subselections
          rest hobject hlookupValid hmerge matchedFieldName
          matchedArguments matchedDirectives matchedSubselections hmatched
      subst matchedFieldName
      exact
        fieldSelectionsWithResponseNameInScope_field_child_branch_forObject
          schema parentType responseName hobject hstack rest htailFeasible
          fieldName matchedArguments matchedDirectives matchedSubselections
          fieldDefinition runtimeType hmatched hlookup hpossible
    simpa [childSource, group, headSelection, mergeSelectionSets,
      Selection.subselections] using
      selectionSetTypeConditionFeasible_append hheadChildFeasible
        hmatchingChildFeasible
  · have htailFree := selectionSetDirectiveFree_tail hfree
    have hsubselectionsFree : selectionSetDirectiveFree subselections :=
      hselectionFree.2
    have hmatchingFree :
        selectionSetDirectiveFree
          (fieldSelectionsWithResponseNameInScope schema parentType responseName rest) :=
      fieldSelectionsWithResponseNameInScope_directiveFree schema parentType
        responseName rest htailFree
    simpa [childSource, group, headSelection, mergeSelectionSets,
      Selection.subselections] using
      selectionSetDirectiveFree_append hsubselectionsFree
        (selectionSetDirectiveFree_mergeSelectionSets hmatchingFree)
  · intro selection hselection
    rcases List.mem_cons.mp hselection with hhead | hmatched
    · subst selection
      refine ⟨sourceField, ?_, rfl, ?_, ?_⟩
      · simp [sourceField, FieldMerge.collectFields, hlookup]
      · simp [sourceField, headSelection, Selection.subselections]
      · intro _hscopedObject
        simp [sourceField]
        exact object_typesOverlapBool_self schema hobject
    · rcases
        fieldSelectionsWithResponseNameInScope_mem_field schema parentType
          responseName rest selection hmatched with
      ⟨matchedFieldName, matchedArguments, matchedDirectives,
        matchedSubselections, hselectionEq⟩
      subst selection
      have hoverlapSelf :
          schema.objectType parentType ->
            schema.typesOverlapBool parentType parentType = true := by
        intro hparentObject
        exact object_typesOverlapBool_self schema hparentObject
      rcases
        fieldSelectionsWithResponseNameInScope_field_mem_collectFields_scoped_lookupValid
          schema parentType parentType responseName rest matchedFieldName
          matchedArguments matchedDirectives matchedSubselections
          hoverlapSelf htailLookup hmatched with
      ⟨scopedField, hscopedRest, hresponse, _hfieldName, _harguments,
        hselectionSet, hoverlap⟩
      refine ⟨scopedField, ?_, hresponse, ?_, hoverlap⟩
      · exact fieldMerge_collectFields_tail_mem schema parentType
          headSelection rest scopedField hscopedRest
      · simpa [Selection.subselections] using hselectionSet
  · simp [childSource, group, headSelection, mergeSelectionSets,
      Selection.subselections]

def NormalizedFieldGroupSource.mapCollectFields
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType : Name}
    {sourceSet targetSet : List Selection}
    {normalized : FieldMerge.ScopedField}
    (hgroup
      : NormalizedFieldGroupSource schema variableDefinitions parentType
          sourceSet normalized)
    (hmap
      : ∀ scopedField,
          scopedField ∈ FieldMerge.collectFields schema parentType sourceSet
          -> scopedField ∈ FieldMerge.collectFields schema parentType targetSet)
    (hsize : SelectionSet.size sourceSet ≤ SelectionSet.size targetSet)
    : NormalizedFieldGroupSource schema variableDefinitions parentType
        targetSet normalized := by
  refine ⟨hgroup.source, hmap hgroup.source hgroup.sourceMem,
    hgroup.sourceRel, hgroup.group, hgroup.childSource,
    hgroup.childSource_eq,
    Nat.lt_of_lt_of_le hgroup.childSource_size_lt hsize,
    hgroup.childReady, hgroup.childLookup, hgroup.childImplementation,
    hgroup.childFeasible, hgroup.childDirectiveFree, ?_,
    hgroup.normalizedSelectionSet⟩
  intro selection hselection
  rcases hgroup.groupScoped selection hselection with
    ⟨scopedField, hscopedMem, hresponse, hselectionSet, hoverlap⟩
  exact ⟨scopedField, hmap scopedField hscopedMem, hresponse,
    hselectionSet, hoverlap⟩

noncomputable def NormalizedFieldGroupSource.mapInlineSomeOverlap
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType typeCondition : Name}
    {directives : List DirectiveApplication}
    {selectionSet rest : List Selection}
    {normalized : FieldMerge.ScopedField}
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hobject : schema.objectType parentType)
    (hpossible : parentType ∈ schema.getPossibleTypes typeCondition)
    (hbodyParentLookup : selectionSetLookupValid schema parentType selectionSet)
    (hbodyTypeLookup : selectionSetLookupValid schema typeCondition selectionSet)
    (hrestLookup : selectionSetLookupValid schema parentType rest)
    (hgroup
      : NormalizedFieldGroupSource schema variableDefinitions parentType
          (selectionSet ++ rest) normalized)
    : NormalizedFieldGroupSource schema variableDefinitions parentType
        (Selection.inlineFragment (some typeCondition) directives selectionSet :: rest)
        normalized := by
  classical
  let targetSet : List Selection :=
    Selection.inlineFragment (some typeCondition) directives selectionSet
      :: rest
  have liftScoped :
      ∀ scopedField,
        scopedField ∈ FieldMerge.collectFields schema parentType
          (selectionSet ++ rest) ->
        { targetField : FieldMerge.ScopedField //
          targetField ∈ FieldMerge.collectFields schema parentType targetSet
            ∧ scopedFieldSameSelection scopedField targetField
            ∧ FieldMerge.sameResponseShape schema scopedField.outputType
              targetField.outputType
            ∧ (targetField.parentType = scopedField.parentType
              ∨ ¬ schema.objectType targetField.parentType) } := by
    intro scopedField hscoped
    have hexists :
        ∃ targetField,
          targetField ∈ FieldMerge.collectFields schema parentType targetSet
            ∧ scopedFieldSameSelection scopedField targetField
            ∧ FieldMerge.sameResponseShape schema scopedField.outputType
              targetField.outputType
            ∧ (targetField.parentType = scopedField.parentType
              ∨ ¬ schema.objectType targetField.parentType) := by
      rw [FieldMerge.collectFields_append] at hscoped
      rcases List.mem_append.mp hscoped with hbody | htail
      · rcases
          fieldMerge_collectFields_objectParent_possibleParent schema
            parentType typeCondition selectionSet scopedField hschema hobject
            hpossible hbodyParentLookup hbodyTypeLookup hbody with
          ⟨targetField, htargetMem, hsame, hshape, hparent⟩
        refine ⟨targetField, ?_, hsame, hshape, hparent⟩
        simp [targetSet, FieldMerge.collectFields, htargetMem]
      · have hshape :
            FieldMerge.sameResponseShape schema scopedField.outputType
              scopedField.outputType :=
          FieldMerge.sameResponseShape_refl schema scopedField.outputType
            (fieldMerge_collectFields_mem_outputType schema parentType rest
              scopedField hschema hrestLookup htail)
        exact ⟨scopedField,
          fieldMerge_collectFields_tail_mem schema parentType
            (Selection.inlineFragment (some typeCondition) directives
              selectionSet)
            rest scopedField htail,
          scopedFieldSameSelection_refl scopedField, hshape, Or.inl rfl⟩
    exact ⟨Classical.choose hexists, Classical.choose_spec hexists⟩
  let sourceLift := liftScoped hgroup.source hgroup.sourceMem
  let targetSource := sourceLift.1
  have htargetSourceMem :
      targetSource ∈ FieldMerge.collectFields schema parentType targetSet :=
    sourceLift.2.1
  have hsourceSame :
      scopedFieldSameSelection hgroup.source targetSource :=
    sourceLift.2.2.1
  have hsourceShape :
      FieldMerge.sameResponseShape schema hgroup.source.outputType
        targetSource.outputType :=
    sourceLift.2.2.2.1
  have hsourceParent :
      targetSource.parentType = hgroup.source.parentType
        ∨ ¬ schema.objectType targetSource.parentType :=
    sourceLift.2.2.2.2
  refine ⟨targetSource, htargetSourceMem, ?_, hgroup.group,
    hgroup.childSource, hgroup.childSource_eq, ?_,
    hgroup.childReady, hgroup.childLookup, hgroup.childImplementation,
    hgroup.childFeasible, hgroup.childDirectiveFree, ?_,
    hgroup.normalizedSelectionSet⟩
  · exact
      GroundTypeNormalization.normalizedFieldSource_of_scopedFieldSameSelection
        hsourceSame hsourceShape hsourceParent hgroup.sourceRel
  · have htargetSize :
        SelectionSet.size (selectionSet ++ rest)
          < SelectionSet.size
              (Selection.inlineFragment (some typeCondition) directives
                selectionSet :: rest) := by
      simp [selectionSet_size_append_for_completeValidity,
        SelectionSet.size, Selection.size]
    exact Nat.lt_trans hgroup.childSource_size_lt htargetSize
  · intro selection hselection
    rcases hgroup.groupScoped selection hselection with
      ⟨scopedField, hscopedMem, hresponse, hselectionSet, hoverlap⟩
    let scopedLift := liftScoped scopedField hscopedMem
    let targetField := scopedLift.1
    have htargetMem :
        targetField ∈ FieldMerge.collectFields schema parentType targetSet :=
      scopedLift.2.1
    have hsame :
        scopedFieldSameSelection scopedField targetField :=
      scopedLift.2.2.1
    have hparent :
        targetField.parentType = scopedField.parentType
          ∨ ¬ schema.objectType targetField.parentType :=
      scopedLift.2.2.2.2
    refine ⟨targetField, htargetMem, ?_, ?_, ?_⟩
    · rcases hsame with ⟨hresponseSame, _hfieldName, _harguments,
        _hselectionSame⟩
      exact hresponseSame.symm.trans hresponse
    · rcases hsame with ⟨_hresponseSame, _hfieldName, _harguments,
        hselectionSame⟩
      exact hselectionSame.symm.trans hselectionSet
    · intro htargetObject
      rcases hparent with hparentEq | htargetNotObject
      · have hscopedObject : schema.objectType scopedField.parentType := by
          simpa [hparentEq] using htargetObject
        simpa [hparentEq] using hoverlap hscopedObject
      · exact False.elim (htargetNotObject htargetObject)

theorem collectFields_normalizeSelectionSet_mem_groupSource_nonempty
    (schema : Schema)
    (variableDefinitions : List VariableDefinition)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    : ∀ parentType selectionSet normalizedField,
      ∀ typeConditions,
        schema.objectType parentType
        -> objectSatisfiesTypeConditionStack schema parentType typeConditions
        -> selectionSetSemanticsReady schema parentType selectionSet
        -> selectionSetLookupValid schema parentType selectionSet
        -> Validation.selectionSetValidInPossibleTypes schema
            variableDefinitions parentType selectionSet
        -> FieldMerge.fieldsInSetCanMerge schema parentType selectionSet
        -> selectionSetDirectiveFree selectionSet
        -> selectionSetTypeConditionFeasible schema parentType typeConditions selectionSet
        -> normalizedField
            ∈ FieldMerge.collectFields schema parentType
                (normalizeSelectionSet schema parentType selectionSet)
        -> Nonempty
            (NormalizedFieldGroupSource schema variableDefinitions
              parentType selectionSet normalizedField) := by
  intro parentType selectionSet
  induction parentType, selectionSet using normalizeSelectionSet.induct schema with
  | case1 parentType =>
      intro normalizedField _typeConditions _hobject _hstack _hready
        _hlookupValid _himplementation _hmerge _hfree _hfeasible hfield
      simp [normalizeSelectionSet, FieldMerge.collectFields] at hfield
  | case2 parentType rest responseName fieldName arguments directives
      subselections hlookup hrest =>
      intro normalizedField typeConditions hobject hstack hready
        hlookupValid himplementation hmerge hfree hfeasible hfield
      have htailReady :
          selectionSetSemanticsReady schema parentType rest :=
        selectionSetSemanticsReady_tail hready
      have htailLookup :
          selectionSetLookupValid schema parentType rest :=
        selectionSetLookupValid_tail hlookupValid
      have htailImplementation :
          Validation.selectionSetValidInPossibleTypes schema
            variableDefinitions parentType rest :=
        GroundTypeNormalization.selectionSetValidInPossibleTypes_tail
          himplementation
      have htailMerge :
          FieldMerge.fieldsInSetCanMerge schema parentType rest :=
        fieldsInSetCanMerge_tail schema parentType
          (Selection.field responseName fieldName arguments directives
            subselections)
          rest hmerge
      have htailFree :
          selectionSetDirectiveFree rest :=
        selectionSetDirectiveFree_tail hfree
      have hfilteredReady :
          selectionSetSemanticsReady schema parentType
            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        selectionSetSemanticsReady_withoutFieldSelectionsWithResponseName schema
          responseName parentType rest htailReady
      have hfilteredLookup :
          selectionSetLookupValid schema parentType
            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        selectionSetLookupValid_withoutFieldSelectionsWithResponseName schema
          responseName parentType rest htailLookup
      have hfilteredImplementation :
          Validation.selectionSetValidInPossibleTypes schema
            variableDefinitions parentType
            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        GroundTypeNormalization.selectionSetValidInPossibleTypes_withoutFieldSelectionsWithResponseName
          schema responseName variableDefinitions parentType rest
          htailImplementation
      have hfilteredMerge :
          FieldMerge.fieldsInSetCanMerge schema parentType
            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        fieldsInSetCanMerge_withoutFieldSelectionsWithResponseName schema
          responseName parentType rest htailMerge
      have hfilteredFree :
          selectionSetDirectiveFree
            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        withoutFieldSelectionsWithResponseName_directiveFree schema responseName rest
          htailFree
      have htailFeasible :
          selectionSetTypeConditionFeasible schema parentType typeConditions
             rest :=
        selectionSetTypeConditionFeasible_tail hfeasible
      have hfilteredFeasible :
          selectionSetTypeConditionFeasible schema parentType typeConditions

            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        selectionSetTypeConditionFeasible_withoutFieldSelectionsWithResponseName
          schema responseName parentType typeConditions rest htailFeasible
      rcases hrest normalizedField typeConditions hobject hstack
          hfilteredReady hfilteredLookup hfilteredImplementation
          hfilteredMerge hfilteredFree hfilteredFeasible
          (by simpa [normalizeSelectionSet, hlookup] using hfield) with
        ⟨restGroup⟩
      exact ⟨NormalizedFieldGroupSource.mapCollectFields restGroup
        (by
          intro scopedField hscopedMem
          exact fieldMerge_collectFields_tail_mem schema parentType
            (Selection.field responseName fieldName arguments directives
              subselections)
            rest scopedField
            (fieldMerge_collectFields_withoutFieldSelectionsWithResponseName_mem
              schema responseName parentType rest scopedField hscopedMem))
        (by
          have hfilteredSize :=
            size_withoutFieldSelectionsWithResponseName_le_for_completeValidity
              schema responseName rest
          have htailSize :=
            selectionSet_size_tail_lt_cons_for_completeValidity
              (Selection.field responseName fieldName arguments directives
                subselections)
              rest
          omega)⟩
  | case3 parentType rest responseName fieldName arguments directives
      subselections fieldDefinition hlookup matching mergedSubselections
      returnType hrest hmerged hpossible =>
      intro candidate typeConditions hobject hstack hready hlookupValid
        himplementation hmerge hfree hfeasible hfieldMem
      let normalizedSubselections :=
        if objectTypeNameBool schema returnType then
          normalizeSelectionSet schema returnType mergedSubselections
        else
          GroundTypeNormalization.possibleTypeNormalizations schema
            (schema.getPossibleTypes returnType) mergedSubselections
      let normalizedHead : FieldMerge.ScopedField := {
        parentType := parentType,
        responseName := responseName,
        fieldName := fieldName,
        arguments := arguments,
        outputType := fieldDefinition.outputType,
        selectionSet := normalizedSubselections
      }
      have htailReady :
          selectionSetSemanticsReady schema parentType rest :=
        selectionSetSemanticsReady_tail hready
      have htailLookup :
          selectionSetLookupValid schema parentType rest :=
        selectionSetLookupValid_tail hlookupValid
      have htailImplementation :
          Validation.selectionSetValidInPossibleTypes schema
            variableDefinitions parentType rest :=
        GroundTypeNormalization.selectionSetValidInPossibleTypes_tail
          himplementation
      have htailMerge :
          FieldMerge.fieldsInSetCanMerge schema parentType rest :=
        fieldsInSetCanMerge_tail schema parentType
          (Selection.field responseName fieldName arguments directives
            subselections)
          rest hmerge
      have htailFree :
          selectionSetDirectiveFree rest :=
        selectionSetDirectiveFree_tail hfree
      have hfilteredReady :
          selectionSetSemanticsReady schema parentType
            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        selectionSetSemanticsReady_withoutFieldSelectionsWithResponseName schema
          responseName parentType rest htailReady
      have hfilteredLookup :
          selectionSetLookupValid schema parentType
            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        selectionSetLookupValid_withoutFieldSelectionsWithResponseName schema
          responseName parentType rest htailLookup
      have hfilteredImplementation :
          Validation.selectionSetValidInPossibleTypes schema
            variableDefinitions parentType
            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        GroundTypeNormalization.selectionSetValidInPossibleTypes_withoutFieldSelectionsWithResponseName
          schema responseName variableDefinitions parentType rest
          htailImplementation
      have hfilteredMerge :
          FieldMerge.fieldsInSetCanMerge schema parentType
            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        fieldsInSetCanMerge_withoutFieldSelectionsWithResponseName schema
          responseName parentType rest htailMerge
      have hfilteredFree :
          selectionSetDirectiveFree
            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        withoutFieldSelectionsWithResponseName_directiveFree schema responseName rest
          htailFree
      have htailFeasible :
          selectionSetTypeConditionFeasible schema parentType typeConditions
             rest :=
        selectionSetTypeConditionFeasible_tail hfeasible
      have hfilteredFeasible :
          selectionSetTypeConditionFeasible schema parentType typeConditions

            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        selectionSetTypeConditionFeasible_withoutFieldSelectionsWithResponseName
          schema responseName parentType typeConditions rest htailFeasible
      have hfieldMem' :
          candidate = normalizedHead
            ∨ candidate ∈ FieldMerge.collectFields schema parentType
              (normalizeSelectionSet schema parentType
                (withoutFieldSelectionsWithResponseName schema responseName rest)) := by
        have hmem :
            candidate ∈ FieldMerge.collectFields schema parentType
              (normalizedField schema returnType responseName fieldName
                arguments directives normalizedSubselections ::
                normalizeSelectionSet schema parentType
                  (withoutFieldSelectionsWithResponseName schema responseName rest)) := by
          rw [normalizeSelectionSet.eq_2, hlookup] at hfieldMem
          change candidate ∈ FieldMerge.collectFields schema parentType
            (normalizedField schema returnType responseName fieldName
              arguments directives normalizedSubselections ::
              normalizeSelectionSet schema parentType
                (withoutFieldSelectionsWithResponseName schema responseName rest))
            at hfieldMem
          exact hfieldMem
        cases hleaf :
            leafTypeNameBool schema returnType
        · cases hnormalizedSubselections : normalizedSubselections with
          | nil =>
              simpa [normalizedField, hleaf, hnormalizedSubselections,
                FieldMerge.collectFields, hlookup, normalizedHead,
                normalizedSubselections] using hmem
          | cons head tail =>
              simpa [normalizedField, hleaf, hnormalizedSubselections,
                FieldMerge.collectFields, hlookup, normalizedHead,
                normalizedSubselections] using hmem
        · simpa [normalizedField, hleaf, FieldMerge.collectFields, hlookup,
            normalizedHead,
            normalizedSubselections] using hmem
      by_cases hhead : candidate = normalizedHead
      · subst candidate
        exact ⟨by
          simpa [normalizedHead, normalizedSubselections,
            returnType, mergeSelectionSets, Selection.subselections] using
            normalizedFieldGroupSource_fieldHead schema variableDefinitions
              parentType
              responseName fieldName arguments directives subselections rest
              fieldDefinition hschema hobject hready htailLookup hlookupValid
              himplementation hmerge hfree hstack hfeasible hlookup⟩
      · have htailMem :
            candidate ∈ FieldMerge.collectFields schema parentType
              (normalizeSelectionSet schema parentType
                (withoutFieldSelectionsWithResponseName schema responseName rest)) := by
          rcases hfieldMem' with hcandidate | htail
          · exact False.elim (hhead hcandidate)
          · exact htail
        rcases hrest candidate typeConditions hobject hstack
            hfilteredReady hfilteredLookup hfilteredImplementation
            hfilteredMerge hfilteredFree hfilteredFeasible
            htailMem with
          ⟨restGroup⟩
        exact ⟨NormalizedFieldGroupSource.mapCollectFields restGroup
          (by
            intro scopedField hscopedMem
            exact fieldMerge_collectFields_tail_mem schema parentType
              (Selection.field responseName fieldName arguments directives
                subselections)
              rest scopedField
              (fieldMerge_collectFields_withoutFieldSelectionsWithResponseName_mem
                schema responseName parentType rest scopedField hscopedMem))
          (by
            have hfilteredSize :=
              size_withoutFieldSelectionsWithResponseName_le_for_completeValidity
                schema responseName rest
            have htailSize :=
              selectionSet_size_tail_lt_cons_for_completeValidity
                (Selection.field responseName fieldName arguments directives
                  subselections)
                rest
            omega)⟩
  | case4 parentType rest directives subselections happend =>
      intro normalizedField typeConditions hobject hstack hready
        hlookupValid himplementation hmerge hfree hfeasible hfieldMem
      have hselectionFree := selectionSetDirectiveFree_head hfree
      have hdirectives : directives = [] := hselectionFree.1
      subst directives
      have hheadReady :
          selectionSemanticsReady schema parentType
            (Selection.inlineFragment none [] subselections) := by
        unfold selectionSetSemanticsReady at hready
        exact hready _ (by simp)
      have hbodyReady :
          selectionSetSemanticsReady schema parentType subselections := by
        simpa [selectionSemanticsReady] using hheadReady
      have htailReady :
          selectionSetSemanticsReady schema parentType rest :=
        selectionSetSemanticsReady_tail hready
      have hheadImplementation :
          Validation.selectionValidInPossibleTypes schema variableDefinitions
            parentType
            (Selection.inlineFragment none [] subselections) :=
        GroundTypeNormalization.selectionSetValidInPossibleTypes_head
          himplementation
      have hbodyImplementation :
          Validation.selectionSetValidInPossibleTypes schema
            variableDefinitions parentType subselections := by
        have hpossible :
            parentType ∈ schema.getPossibleTypes parentType :=
          List.contains_iff_mem.mp
            (object_typeIncludesObjectBool_self schema hobject)
        simpa using hheadImplementation parentType hpossible
      have htailImplementation :
          Validation.selectionSetValidInPossibleTypes schema
            variableDefinitions parentType rest :=
        GroundTypeNormalization.selectionSetValidInPossibleTypes_tail
          himplementation
      have hbodyTailImplementation :
          Validation.selectionSetValidInPossibleTypes schema
            variableDefinitions parentType (subselections ++ rest) :=
        GroundTypeNormalization.selectionSetValidInPossibleTypes_append
          hbodyImplementation htailImplementation
      have hbodyTailMerge :
          FieldMerge.fieldsInSetCanMerge schema parentType
            (subselections ++ rest) :=
        fieldsInSetCanMerge_inlineFragment_none_flatten schema parentType
          subselections rest hmerge
      have htailFree := selectionSetDirectiveFree_tail hfree
      have hbodyTailFree :
          selectionSetDirectiveFree (subselections ++ rest) :=
        selectionSetDirectiveFree_append hselectionFree.2 htailFree
      have hheadLookup :
          selectionLookupValid schema parentType
            (Selection.inlineFragment none [] subselections) :=
        selectionSetLookupValid_head hlookupValid
      have hbodyLookup :
          selectionSetLookupValid schema parentType subselections := by
        simpa [selectionLookupValid] using hheadLookup
      have htailLookup :
          selectionSetLookupValid schema parentType rest :=
        selectionSetLookupValid_tail hlookupValid
      have hbodyTailReady :
          selectionSetSemanticsReady schema parentType
            (subselections ++ rest) :=
        selectionSetSemanticsReady_append hbodyReady htailReady
      have hbodyTailLookup :
          selectionSetLookupValid schema parentType
            (subselections ++ rest) :=
        selectionSetLookupValid_append hbodyLookup htailLookup
      have hbodyFeasible :
          selectionSetTypeConditionFeasible schema parentType typeConditions
             subselections := by
        simpa [selectionSetTypeConditionFeasible,
          selectionTypeConditionFeasible] using hfeasible.1
      have htailFeasible :
          selectionSetTypeConditionFeasible schema parentType typeConditions
             rest :=
        selectionSetTypeConditionFeasible_tail hfeasible
      have hbodyTailFeasible :
          selectionSetTypeConditionFeasible schema parentType typeConditions
             (subselections ++ rest) :=
        selectionSetTypeConditionFeasible_append hbodyFeasible htailFeasible
      rcases happend normalizedField typeConditions hobject hstack
          hbodyTailReady hbodyTailLookup hbodyTailImplementation
          hbodyTailMerge hbodyTailFree hbodyTailFeasible
          (by simpa [normalizeSelectionSet] using hfieldMem) with
        ⟨bodyTailGroup⟩
      exact ⟨NormalizedFieldGroupSource.mapCollectFields bodyTailGroup
        (by
          intro scopedField hscopedMem
          simpa [FieldMerge.collectFields, FieldMerge.collectFields_append]
            using hscopedMem)
        (by
          simp [selectionSet_size_append_for_completeValidity,
            SelectionSet.size, Selection.size]
          )⟩
  | case5 parentType rest typeCondition directives subselections hoverlap
      _hrest happend =>
      intro normalizedField typeConditions hobject hstack hready
        hlookupValid himplementation hmerge hfree hfeasible hfieldMem
      have hselectionFree := selectionSetDirectiveFree_head hfree
      have hdirectives : directives = [] := hselectionFree.1
      subst directives
      have hheadReady :
          selectionSemanticsReady schema parentType
            (Selection.inlineFragment (some typeCondition) []
              subselections) := by
        unfold selectionSetSemanticsReady at hready
        exact hready _ (by simp)
      have hbodyReady :
          selectionSetSemanticsReady schema parentType subselections := by
        have hpair :
            selectionSetLookupValid schema typeCondition subselections
              ∧ (schema.typesOverlapBool parentType typeCondition = true ->
                selectionSetSemanticsReady schema parentType subselections) := by
          simpa [selectionSemanticsReady] using hheadReady
        exact hpair.2 hoverlap
      have hbodyTypeLookup :
          selectionSetLookupValid schema typeCondition subselections := by
        have hpair :
            selectionSetLookupValid schema typeCondition subselections
              ∧ (schema.typesOverlapBool parentType typeCondition = true ->
                selectionSetSemanticsReady schema parentType subselections) := by
          simpa [selectionSemanticsReady] using hheadReady
        exact hpair.1
      have hbodyParentLookup :
          selectionSetLookupValid schema parentType subselections :=
        selectionSetLookupValid_of_selectionSetSemanticsReady subselections
          hbodyReady
      have htailReady :
          selectionSetSemanticsReady schema parentType rest :=
        selectionSetSemanticsReady_tail hready
      have hheadImplementation :
          Validation.selectionValidInPossibleTypes schema variableDefinitions
            parentType
            (Selection.inlineFragment (some typeCondition) []
              subselections) :=
        GroundTypeNormalization.selectionSetValidInPossibleTypes_head
          himplementation
      have hfragmentImplementation :
          ∀ objectType,
            objectType ∈ schema.getPossibleTypes typeCondition ->
              Validation.selectionSetValidInPossibleTypes schema
                variableDefinitions objectType subselections := by
        simpa [Validation.selectionValidInPossibleTypes] using
          hheadImplementation hoverlap
      have hpossible :
          parentType ∈ schema.getPossibleTypes typeCondition :=
        List.contains_iff_mem.mp
          (typeIncludesObjectBool_of_object_typesOverlapBool schema
            hobject hoverlap)
      have hbodyImplementation :
          Validation.selectionSetValidInPossibleTypes schema
            variableDefinitions parentType subselections :=
        hfragmentImplementation parentType hpossible
      have htailImplementation :
          Validation.selectionSetValidInPossibleTypes schema
            variableDefinitions parentType rest :=
        GroundTypeNormalization.selectionSetValidInPossibleTypes_tail
          himplementation
      have hbodyTailImplementation :
          Validation.selectionSetValidInPossibleTypes schema
            variableDefinitions parentType (subselections ++ rest) :=
        GroundTypeNormalization.selectionSetValidInPossibleTypes_append
          hbodyImplementation htailImplementation
      have htailLookup :
          selectionSetLookupValid schema parentType rest :=
        selectionSetLookupValid_tail hlookupValid
      have hbodyTailReady :
          selectionSetSemanticsReady schema parentType
            (subselections ++ rest) :=
        selectionSetSemanticsReady_append hbodyReady htailReady
      have hbodyTailLookup :
          selectionSetLookupValid schema parentType
            (subselections ++ rest) :=
        selectionSetLookupValid_append hbodyParentLookup htailLookup
      have hbodyTailMerge :
          FieldMerge.fieldsInSetCanMerge schema parentType
            (subselections ++ rest) :=
        fieldsInSetCanMerge_inlineFragment_some_overlap_flatten_object
          schema parentType typeCondition subselections rest hschema hobject
          hoverlap hbodyParentLookup hbodyTypeLookup htailLookup hmerge
      have htailFree := selectionSetDirectiveFree_tail hfree
      have hbodyTailFree :
          selectionSetDirectiveFree (subselections ++ rest) :=
        selectionSetDirectiveFree_append hselectionFree.2 htailFree
      have hbodyFeasible :
          selectionSetTypeConditionFeasible schema parentType
            (typeCondition :: typeConditions)  subselections := by
        simpa [selectionSetTypeConditionFeasible,
          selectionTypeConditionFeasible] using hfeasible.1
      have htailFeasible :
          selectionSetTypeConditionFeasible schema parentType typeConditions
             rest :=
        selectionSetTypeConditionFeasible_tail hfeasible
      have hbodyFeasibleInOuterStack :
          selectionSetTypeConditionFeasible schema parentType typeConditions
            subselections :=
        selectionSetTypeConditionFeasible_of_stack_subset schema
          (fun candidate hcandidate =>
            List.mem_cons_of_mem typeCondition hcandidate)
          subselections hbodyFeasible
      have hbodyTailFeasible :
          selectionSetTypeConditionFeasible schema parentType typeConditions
            (subselections ++ rest) :=
        selectionSetTypeConditionFeasible_append hbodyFeasibleInOuterStack
          htailFeasible
      rcases happend normalizedField typeConditions
          hobject hstack hbodyTailReady hbodyTailLookup
          hbodyTailImplementation hbodyTailMerge hbodyTailFree
          hbodyTailFeasible
          (by simpa [normalizeSelectionSet, hoverlap] using hfieldMem) with
        ⟨bodyTailGroup⟩
      exact ⟨NormalizedFieldGroupSource.mapInlineSomeOverlap
        hschema hobject hpossible hbodyParentLookup hbodyTypeLookup
        htailLookup bodyTailGroup⟩
  | case6 parentType rest typeCondition directives subselections hoverlap
      hrest =>
      intro normalizedField typeConditions hobject hstack hready
        hlookupValid himplementation hmerge hfree hfeasible hfieldMem
      have htailReady :
          selectionSetSemanticsReady schema parentType rest :=
        selectionSetSemanticsReady_tail hready
      have htailLookup :
          selectionSetLookupValid schema parentType rest :=
        selectionSetLookupValid_tail hlookupValid
      have htailImplementation :
          Validation.selectionSetValidInPossibleTypes schema
            variableDefinitions parentType rest :=
        GroundTypeNormalization.selectionSetValidInPossibleTypes_tail
          himplementation
      have htailMerge :
          FieldMerge.fieldsInSetCanMerge schema parentType rest :=
        fieldsInSetCanMerge_tail schema parentType
          (Selection.inlineFragment (some typeCondition) directives
            subselections)
          rest hmerge
      have htailFree :
          selectionSetDirectiveFree rest :=
        selectionSetDirectiveFree_tail hfree
      have hfalse :
          schema.typesOverlapBool parentType typeCondition = false := by
        cases hmatch : schema.typesOverlapBool parentType typeCondition
        · rfl
        · contradiction
      have htailFeasible :
          selectionSetTypeConditionFeasible schema parentType typeConditions
             rest :=
        selectionSetTypeConditionFeasible_tail hfeasible
      rcases hrest normalizedField typeConditions hobject hstack htailReady
          htailLookup htailImplementation htailMerge htailFree htailFeasible
          (by simpa [normalizeSelectionSet, hfalse] using hfieldMem) with
        ⟨restGroup⟩
      exact ⟨NormalizedFieldGroupSource.mapCollectFields restGroup
        (by
          intro scopedField hscopedMem
          exact fieldMerge_collectFields_tail_mem schema parentType
            (Selection.inlineFragment (some typeCondition) directives
              subselections)
            rest scopedField hscopedMem)
        (by
          exact Nat.le_of_lt
            (selectionSet_size_tail_lt_cons_for_completeValidity
              (Selection.inlineFragment (some typeCondition) directives
                subselections)
              rest))⟩

noncomputable def collectFields_normalizeSelectionSet_mem_groupSource
    (schema : Schema)
    (variableDefinitions : List VariableDefinition)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (parentType : Name) (selectionSet : List Selection)
    (normalizedField : FieldMerge.ScopedField)
    : schema.objectType parentType
      -> selectionSetSemanticsReady schema parentType selectionSet
      -> selectionSetLookupValid schema parentType selectionSet
      -> Validation.selectionSetValidInPossibleTypes schema
          variableDefinitions parentType selectionSet
      -> FieldMerge.fieldsInSetCanMerge schema parentType selectionSet
      -> selectionSetDirectiveFree selectionSet
      -> selectionSetTypeConditionFeasible schema parentType [parentType] selectionSet
      -> normalizedField
          ∈ FieldMerge.collectFields schema parentType
              (normalizeSelectionSet schema parentType selectionSet)
      -> NormalizedFieldGroupSource schema variableDefinitions parentType
          selectionSet
          normalizedField := by
  intro hobject hready hlookupValid himplementation hmerge hfree hfeasible
    hfield
  have hstack :
      objectSatisfiesTypeConditionStack schema parentType [parentType] :=
    objectSatisfiesTypeConditionStack_singleton_of_object_forValidity
      schema hobject
  exact Classical.choice
    (collectFields_normalizeSelectionSet_mem_groupSource_nonempty schema
      variableDefinitions hschema parentType selectionSet normalizedField
      [parentType] hobject hstack hready hlookupValid himplementation hmerge
      hfree hfeasible hfield)

theorem fieldsInSetCanMerge_groupSources_rawChildSource_pair
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType objectType : Name)
    {leftSet rightSet : List Selection}
    {leftField rightField : FieldMerge.ScopedField}
    (hleftGroup
      : NormalizedFieldGroupSource schema variableDefinitions parentType
          leftSet leftField)
    (hrightGroup
      : NormalizedFieldGroupSource schema variableDefinitions parentType
          rightSet rightField)
    : schema.objectType parentType
      -> FieldMerge.fieldsInSetCanMerge schema parentType (leftSet ++ rightSet)
      -> leftField.responseName = rightField.responseName
      -> FieldMerge.fieldsInSetCanMerge schema objectType
          (hleftGroup.childSource ++ hrightGroup.childSource) := by
  intro hobject hsourcePair hresponse
  have hscopedOf :
      ∀ selection, selection ∈ hleftGroup.group ++ hrightGroup.group ->
        ∃ scopedField,
          scopedField ∈ FieldMerge.collectFields schema parentType
            (leftSet ++ rightSet)
            ∧ scopedField.responseName = leftField.responseName
            ∧ scopedField.selectionSet = selection.subselections
            ∧ (schema.objectType scopedField.parentType ->
              schema.typesOverlapBool parentType scopedField.parentType =
                true) := by
    intro selection hselection
    rcases List.mem_append.mp hselection with hleftSelection | hrightSelection
    · rcases hleftGroup.groupScoped selection hleftSelection with
        ⟨scopedField, hscopedMem, hscopedResponse, hselectionSet,
          hoverlap⟩
      refine ⟨scopedField, ?_, hscopedResponse, hselectionSet, hoverlap⟩
      rw [FieldMerge.collectFields_append]
      exact List.mem_append_left
        (FieldMerge.collectFields schema parentType rightSet) hscopedMem
    · rcases hrightGroup.groupScoped selection hrightSelection with
        ⟨scopedField, hscopedMem, hscopedResponse, hselectionSet,
          hoverlap⟩
      refine ⟨scopedField, ?_, ?_, hselectionSet, hoverlap⟩
      · rw [FieldMerge.collectFields_append]
        exact List.mem_append_right
          (FieldMerge.collectFields schema parentType leftSet) hscopedMem
      · exact hscopedResponse.trans hresponse.symm
  have hraw :
      FieldMerge.fieldsInSetCanMerge schema objectType
        (mergeSelectionSets hleftGroup.group ++
          mergeSelectionSets hrightGroup.group) :=
    fieldsInSetCanMerge_mergeSelectionSets_pair_of_scoped schema
      parentType leftField.responseName objectType (leftSet ++ rightSet)
      hleftGroup.group hrightGroup.group hobject hsourcePair hscopedOf
  simpa [hleftGroup.childSource_eq, hrightGroup.childSource_eq] using hraw

end CompleteNormalization

end NormalForm

end GraphQL
