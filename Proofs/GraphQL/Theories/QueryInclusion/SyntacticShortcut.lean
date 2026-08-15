import Proofs.GraphQL.Theories.QueryInclusion.RegionSearch

/-! Soundness of the conservative syntax-only query-inclusion shortcut. -/

namespace GraphQL
namespace QueryInclusion

open Execution
open Execution.FieldGroups

structure ExecutableFieldSyntacticallyIncludes (left right : ExecutableField) : Prop where
  parentType : left.parentType = right.parentType
  responseName : left.responseName = right.responseName
  fieldName : left.fieldName = right.fieldName
  arguments : Argument.argumentsEquivalent left.arguments right.arguments
  selectionSet
    : selectionSetSyntacticallyIncludesBool left.selectionSet right.selectionSet = true

theorem selectionSetSyntacticallyIncludesBool_iff (left right : List Selection)
    : selectionSetSyntacticallyIncludesBool left right = true
      ↔ ∀ rightSelection,
          rightSelection ∈ right
          -> ∃ leftSelection,
              leftSelection ∈ left
              ∧ selectionSyntacticallyIncludesBool leftSelection rightSelection
                = true := by
  induction right with
  | nil => simp [selectionSetSyntacticallyIncludesBool]
  | cons rightSelection rest ih =>
      simp only [selectionSetSyntacticallyIncludesBool, Bool.and_eq_true, ih,
        List.mem_cons, forall_eq_or_imp]
      constructor
      · rintro ⟨hhead, hrest⟩
        exact ⟨List.any_eq_true.mp hhead, hrest⟩
      · rintro ⟨hhead, hrest⟩
        exact ⟨List.any_eq_true.mpr hhead, hrest⟩

theorem selectionSetSyntacticallyIncludesBool_eq_of_perm
    {left reorderedLeft right reorderedRight : List Selection}
    (hleft : left.Perm reorderedLeft) (hright : right.Perm reorderedRight)
    : selectionSetSyntacticallyIncludesBool left right
      = selectionSetSyntacticallyIncludesBool reorderedLeft reorderedRight := by
  apply Bool.eq_iff_iff.mpr
  rw [selectionSetSyntacticallyIncludesBool_iff,
    selectionSetSyntacticallyIncludesBool_iff]
  constructor
  · intro hincludes rightSelection hrightSelection
    rcases hincludes rightSelection (hright.mem_iff.mpr hrightSelection) with
      ⟨leftSelection, hleftSelection, hselection⟩
    exact ⟨leftSelection, hleft.mem_iff.mp hleftSelection, hselection⟩
  · intro hincludes rightSelection hrightSelection
    rcases hincludes rightSelection (hright.mem_iff.mp hrightSelection) with
      ⟨leftSelection, hleftSelection, hselection⟩
    exact ⟨leftSelection, hleft.mem_iff.mpr hleftSelection, hselection⟩

theorem selectionSetResponseDepth_eq_of_perm
    {left right : List Selection} (hperm : left.Perm right)
    : selectionSetResponseDepth left = selectionSetResponseDepth right := by
  induction hperm with
  | nil => rfl
  | cons selection _rest ih => simp [selectionSetResponseDepth, ih]
  | swap first second rest =>
      simp only [selectionSetResponseDepth]
      omega
  | trans _ _ ihleft ihright => exact ihleft.trans ihright

theorem selectionSetSyntacticInclusionShortcutBool_of_perm
    {fuel : Nat} {left reorderedLeft right reorderedRight : List Selection}
    (hleft : left.Perm reorderedLeft) (hright : right.Perm reorderedRight)
    (hcheck : selectionSetSyntacticInclusionShortcutBool fuel left right = true)
    : selectionSetSyntacticInclusionShortcutBool fuel reorderedLeft reorderedRight
      = true := by
  simp only [selectionSetSyntacticInclusionShortcutBool, Bool.and_eq_true,
    decide_eq_true_iff] at hcheck ⊢
  exact ⟨by simpa [selectionSetResponseDepth_eq_of_perm hright] using hcheck.1,
    by
      rw [← selectionSetSyntacticallyIncludesBool_eq_of_perm hleft hright]
      exact hcheck.2⟩

private theorem selection_size_le_selectionSet_size_of_mem
    {selection : Selection} {selectionSet : List Selection}
    (hmember : selection ∈ selectionSet)
    : selection.size ≤ SelectionSet.size selectionSet := by
  induction selectionSet with
  | nil => simp at hmember
  | cons head rest ih =>
      rcases List.mem_cons.mp hmember with rfl | hrest
      · simp [SelectionSet.size]
      · exact Nat.le_trans (ih hrest) (by simp [SelectionSet.size])

mutual
  theorem collectFlatSelection_syntactically_includes
      (schema : Schema) (variableValues : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectRef)
      (left right : Selection)
      (hsyntax : selectionSyntacticallyIncludesBool left right = true)
      : ∀ rightField,
          rightField ∈ collectFlatSelection schema variableValues parentType source right
          -> ∃ leftField,
              leftField
                ∈ collectFlatSelection schema variableValues parentType source left
              ∧ ExecutableFieldSyntacticallyIncludes leftField rightField := by
    cases left with
    | field leftResponseName leftFieldName leftArguments leftDirectives
        leftSelectionSet =>
        cases right with
        | field rightResponseName rightFieldName rightArguments rightDirectives
            rightSelectionSet =>
            simp only [selectionSyntacticallyIncludesBool, Bool.and_eq_true] at hsyntax
            have hresponseName := hsyntax.1.1.1.1
            have hfieldName := hsyntax.1.1.1.2
            have harguments := hsyntax.1.1.2
            have hdirectives := hsyntax.1.2
            have hselectionSet := hsyntax.2
            clear hsyntax
            have hresponseNameEq : leftResponseName = rightResponseName :=
              beq_iff_eq.mp hresponseName
            have hfieldNameEq : leftFieldName = rightFieldName :=
              beq_iff_eq.mp hfieldName
            have hdirectivesEq : leftDirectives = rightDirectives :=
              Algorithms.directiveListEqBool_eq hdirectives
            subst rightResponseName
            subst rightFieldName
            subst rightDirectives
            intro rightField hrightField
            cases hallows
                  : selectionDirectivesAllowBool variableValues leftDirectives with
            | false =>
                simp [collectFlatSelection, hallows] at hrightField
            | true =>
                simp only [collectFlatSelection, hallows, if_true, List.mem_singleton]
                  at hrightField ⊢
                subst rightField
                refine ⟨_, rfl, ?_⟩
                exact {
                  parentType := rfl
                  responseName := rfl
                  fieldName := rfl
                  arguments :=
                    (argumentsSyntacticallyEquivalentBool_iff _ _).mp harguments
                  selectionSet := hselectionSet
                }
        | inlineFragment _ _ _ => simp [selectionSyntacticallyIncludesBool] at hsyntax
    | inlineFragment leftTypeCondition leftDirectives leftSelectionSet =>
        cases right with
        | field _ _ _ _ _ => simp [selectionSyntacticallyIncludesBool] at hsyntax
        | inlineFragment rightTypeCondition rightDirectives rightSelectionSet =>
            simp only [selectionSyntacticallyIncludesBool, Bool.and_eq_true] at hsyntax
            have htypeCondition := hsyntax.1.1
            have hdirectives := hsyntax.1.2
            have hselectionSet := hsyntax.2
            clear hsyntax
            have htypeConditionEq : leftTypeCondition = rightTypeCondition :=
              beq_iff_eq.mp htypeCondition
            have hdirectivesEq : leftDirectives = rightDirectives :=
              Algorithms.directiveListEqBool_eq hdirectives
            subst rightTypeCondition
            subst rightDirectives
            cases leftTypeCondition with
            | none =>
                cases hallows
                      : selectionDirectivesAllowBool variableValues leftDirectives with
                | false =>
                    simp [collectFlatSelection, hallows]
                | true =>
                    simpa [collectFlatSelection, hallows] using
                      collectFlatFields_syntactically_includes schema variableValues
                        parentType source leftSelectionSet rightSelectionSet hselectionSet
            | some typeCondition =>
                cases hallows
                      : selectionDirectivesAllowBool variableValues leftDirectives with
                | false =>
                    simp [collectFlatSelection, hallows]
                | true =>
                    cases happlies
                          : doesFragmentTypeApplyBool schema parentType source
                              typeCondition with
                    | false =>
                        simp [collectFlatSelection, hallows, happlies]
                    | true =>
                        simpa [collectFlatSelection, hallows, happlies] using
                          collectFlatFields_syntactically_includes schema variableValues
                            parentType source leftSelectionSet rightSelectionSet
                            hselectionSet
  termination_by 2 * right.size
  decreasing_by
    all_goals simp_all [Selection.size]
    all_goals first
      | omega
      | have hle := selection_size_le_selectionSet_size_of_mem hrightSelection
        omega

  theorem collectFlatFields_syntactically_includes
      (schema : Schema) (variableValues : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectRef)
      (left right : List Selection)
      (hsyntax : selectionSetSyntacticallyIncludesBool left right = true)
      : ∀ rightField,
          rightField ∈ collectFlatFields schema variableValues parentType source right
          -> ∃ leftField,
              leftField ∈ collectFlatFields schema variableValues parentType source left
              ∧ ExecutableFieldSyntacticallyIncludes leftField rightField := by
    intro rightField hrightField
    rw [collectFlatFields_eq_flatMap_collectFlatSelection] at hrightField ⊢
    rcases List.mem_flatMap.mp hrightField with
      ⟨rightSelection, hrightSelection, hrightField⟩
    rcases (selectionSetSyntacticallyIncludesBool_iff left right).mp hsyntax
        rightSelection hrightSelection with
      ⟨leftSelection, hleftSelection, hselection⟩
    rcases collectFlatSelection_syntactically_includes schema variableValues
        parentType source leftSelection rightSelection hselection rightField hrightField with
      ⟨leftField, hleftField, hincludes⟩
    exact ⟨leftField, List.mem_flatMap.mpr
      ⟨leftSelection, hleftSelection, hleftField⟩, hincludes⟩
  termination_by 2 * SelectionSet.size right + 1
  decreasing_by
    all_goals
      have hle := selection_size_le_selectionSet_size_of_mem hrightSelection
      omega
end

theorem collectFields_syntactically_includes
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectRef)
    (left right : List Selection)
    (hsyntax : selectionSetSyntacticallyIncludesBool left right = true)
    : ∀ rightField,
        rightField
          ∈ flattenCollectedFields
              (collectFields schema variableValues parentType source right)
        -> ∃ leftField,
            leftField
              ∈ flattenCollectedFields
                  (collectFields schema variableValues parentType source left)
            ∧ ExecutableFieldSyntacticallyIncludes leftField rightField := by
  intro rightField hrightField
  have hrightFlat : rightField ∈
      collectFlatFields schema variableValues parentType source right :=
    (collectFlatFields_perm_flatten_collectFields schema variableValues parentType
      source right).mem_iff.mpr hrightField
  rcases collectFlatFields_syntactically_includes schema variableValues parentType
      source left right hsyntax rightField hrightFlat with
    ⟨leftField, hleftFlat, hincludes⟩
  exact ⟨leftField,
    (collectFlatFields_perm_flatten_collectFields schema variableValues parentType
      source left).mem_iff.mp hleftFlat,
    hincludes⟩

theorem syntacticallyIncludedMergedSelectionSets
    {leftFields rightFields : List ExecutableField}
    (hfields
      : ∀ rightField,
          rightField ∈ rightFields
          -> ∃ leftField,
              leftField ∈ leftFields
              ∧ ExecutableFieldSyntacticallyIncludes leftField rightField)
    : selectionSetSyntacticallyIncludesBool
        (executableFieldsMergedSelectionSet leftFields)
        (executableFieldsMergedSelectionSet rightFields)
      = true := by
  apply (selectionSetSyntacticallyIncludesBool_iff _ _).mpr
  intro rightSelection hrightSelection
  rw [executableFieldsMergedSelectionSet] at hrightSelection ⊢
  rcases List.mem_flatMap.mp hrightSelection with
    ⟨rightField, hrightField, hrightSelection⟩
  rcases hfields rightField hrightField with
    ⟨leftField, hleftField, hincludes⟩
  rcases (selectionSetSyntacticallyIncludesBool_iff _ _).mp hincludes.selectionSet
      rightSelection hrightSelection with
    ⟨leftSelection, hleftSelection, hselection⟩
  exact ⟨leftSelection, List.mem_flatMap.mpr
    ⟨leftField, hleftField, hleftSelection⟩, hselection⟩

theorem collectFields_syntactically_included_group
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectRef)
    (left right : List Selection)
    (hsyntax : selectionSetSyntacticallyIncludesBool left right = true)
    (rightName : Name) (rightFields : List ExecutableField)
    (hrightGroup
      : (rightName, rightFields)
        ∈ collectFields schema variableValues parentType source right)
    : ∃ leftFields,
        (rightName, leftFields)
          ∈ collectFields schema variableValues parentType source left
        ∧ ∀ rightField,
            rightField ∈ rightFields
            -> ∃ leftField,
                leftField ∈ leftFields
                ∧ ExecutableFieldSyntacticallyIncludes leftField rightField := by
  let leftGroups := collectFields schema variableValues parentType source left
  let rightGroups := collectFields schema variableValues parentType source right
  have hleftWellFormed :=
    NormalForm.GroundTypeNormalization.collectFields_wellFormed schema variableValues
      parentType source left
  have hrightWellFormed :=
    NormalForm.GroundTypeNormalization.collectFields_wellFormed schema variableValues
      parentType source right
  have hleftKeysNodup :=
    (executableGroupNamesNodup_iff_map_fst_nodup leftGroups).mp
      (NormalForm.collectFields_namesNodup schema variableValues parentType source left)
  have hcover := collectFields_syntactically_includes schema variableValues parentType
    source left right hsyntax
  have hrightNonempty := (hrightWellFormed (rightName, rightFields) hrightGroup).1
  cases hrightFieldsEq : rightFields with
  | nil => exact False.elim (hrightNonempty hrightFieldsEq)
  | cons rightHead rightRest =>
      have hrightHead : rightHead ∈ rightFields := by simp [hrightFieldsEq]
      have hrightHeadFlat : rightHead ∈ flattenCollectedFields rightGroups :=
        (mem_flattenCollectedFields_iff rightGroups rightHead).mpr
          ⟨rightName, rightFields, hrightGroup, hrightHead⟩
      rcases hcover rightHead hrightHeadFlat with
        ⟨leftWitness, hleftWitnessFlat, hwitness⟩
      rcases (mem_flattenCollectedFields_iff leftGroups leftWitness).mp
          hleftWitnessFlat with
        ⟨leftName, leftFields, hleftGroup, hleftWitness⟩
      have hleftWitnessName : leftWitness.responseName = leftName :=
        (hleftWellFormed (leftName, leftFields) hleftGroup).2 leftWitness
          hleftWitness
      have hrightHeadName : rightHead.responseName = rightName :=
        (hrightWellFormed (rightName, rightFields) hrightGroup).2 rightHead
          hrightHead
      have hleftName : leftName = rightName := by
        rw [← hleftWitnessName, hwitness.responseName, hrightHeadName]
      refine ⟨leftFields, ?_, ?_⟩
      · simpa [leftGroups, hleftName] using hleftGroup
      intro rightField hrightField
      have hrightFieldOriginal : rightField ∈ rightFields := by
        simpa [hrightFieldsEq] using hrightField
      have hrightFieldFlat : rightField ∈ flattenCollectedFields rightGroups :=
        (mem_flattenCollectedFields_iff rightGroups rightField).mpr
          ⟨rightName, rightFields, hrightGroup, hrightFieldOriginal⟩
      rcases hcover rightField hrightFieldFlat with
        ⟨leftField, hleftFieldFlat, hincludes⟩
      rcases (mem_flattenCollectedFields_iff leftGroups leftField).mp
          hleftFieldFlat with
        ⟨candidateName, candidateFields, hcandidateGroup, hcandidateField⟩
      have hcandidateFieldName : leftField.responseName = candidateName :=
        (hleftWellFormed (candidateName, candidateFields) hcandidateGroup).2
          leftField hcandidateField
      have hrightFieldName : rightField.responseName = rightName :=
        (hrightWellFormed (rightName, rightFields) hrightGroup).2 rightField
          hrightFieldOriginal
      have hcandidateName : candidateName = leftName := by
        rw [← hcandidateFieldName, hincludes.responseName, hrightFieldName,
          ← hleftName]
      have hgroupEq : (candidateName, candidateFields) = (leftName, leftFields) :=
        pair_eq_of_map_fst_nodup hleftKeysNodup hcandidateGroup hleftGroup
          hcandidateName
      injection hgroupEq with _ hfieldsEq
      subst candidateFields
      exact ⟨leftField, hcandidateField, hincludes⟩

theorem selectionSetSyntacticInclusionShortcutBool_sound
    (schema : Schema) (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (fuel : Nat) (parentType : Name) (variableValues : VariableValues)
    (left right : List Selection)
    (hparentObject : schema.objectType parentType)
    (hleftReady : NormalForm.selectionSetSemanticsReady schema parentType left)
    (hleftMerge : FieldMerge.fieldsInSetCanMerge schema parentType left)
    (hrightReady : NormalForm.selectionSetSemanticsReady schema parentType right)
    (hrightMerge : FieldMerge.fieldsInSetCanMerge schema parentType right)
    (hcheck : selectionSetSyntacticInclusionShortcutBool fuel left right = true)
    : selectionSetIncludesBoolWithFuel schema fuel parentType variableValues left right
      = true := by
  simp only [selectionSetSyntacticInclusionShortcutBool, Bool.and_eq_true,
    decide_eq_true_iff] at hcheck
  rcases hcheck with ⟨hdepth, hsyntax⟩
  induction fuel generalizing parentType left right with
  | zero =>
      rw [selectionSetIncludesBoolWithFuel,
        getPossibleTypes_eq_singleton_of_object schema hparentObject]
      simp only [List.all_cons, List.all_nil, Bool.and_true,
        selectionSetIncludesAtRuntimeBoolWithFuel]
      apply List.isEmpty_iff.mpr
      let rightGroups := collectRuntimeFieldGroups schema variableValues parentType
        parentType right
      change rightGroups = []
      cases hgroups : rightGroups with
      | nil => rfl
      | cons group rest =>
          rcases group with ⟨responseName, fields⟩
          have hgroupsReady := executableGroupsSemanticsReady_collectFields schema
            variableValues parentType PUnit.unit right hparentObject hrightReady
            hrightMerge
          have hgroupReady := hgroupsReady responseName fields (by
            simpa [rightGroups, collectRuntimeFieldGroups] using
              show (responseName, fields) ∈ rightGroups by simp [hgroups])
          cases hfields : fields with
          | nil => exact False.elim (hgroupReady.1 hfields)
          | cons field fields =>
              have hbound := collectFields_responseDepth_bound schema variableValues
                parentType (ResolverValue.object parentType PUnit.unit) right
              have hgroupMem : (responseName, field :: fields) ∈
                  collectFields schema variableValues parentType
                    (ResolverValue.object parentType PUnit.unit) right := by
                simpa [rightGroups, collectRuntimeFieldGroups] using
                  show (responseName, field :: fields) ∈ rightGroups by
                    simp [hgroups, hfields]
              have hfieldFlat : field ∈
                  (collectFields schema variableValues parentType
                    (ResolverValue.object parentType PUnit.unit) right).flatMap Prod.snd := by
                exact List.mem_flatMap.mpr
                  ⟨(responseName, field :: fields), hgroupMem, by simp⟩
              have := hbound field hfieldFlat
              omega
  | succ childFuel ih =>
      rw [selectionSetIncludesBoolWithFuel,
        getPossibleTypes_eq_singleton_of_object schema hparentObject]
      simp only [List.all_cons, List.all_nil, Bool.and_true,
        selectionSetIncludesAtRuntimeBoolWithFuel]
      let source : ResolverValue PUnit := .object parentType PUnit.unit
      let leftGroups := collectRuntimeFieldGroups schema variableValues parentType
        parentType left
      let rightGroups := collectRuntimeFieldGroups schema variableValues parentType
        parentType right
      have hleftGroupsReady := executableGroupsSemanticsReady_collectFields schema
        variableValues parentType PUnit.unit left hparentObject hleftReady hleftMerge
      have hrightGroupsReady := executableGroupsSemanticsReady_collectFields schema
        variableValues parentType PUnit.unit right hparentObject hrightReady hrightMerge
      apply List.all_eq_true.mpr
      intro rightGroup hrightGroup
      cases rightGroup
      rename_i rightName rightFields
      have hrightGroup' : (rightName, rightFields) ∈
          collectFields schema variableValues parentType source right := by
        simpa [rightGroups, source, collectRuntimeFieldGroups] using hrightGroup
      rcases collectFields_syntactically_included_group schema variableValues parentType
          source left right hsyntax rightName rightFields hrightGroup' with
        ⟨leftFields, hleftGroup, hfields⟩
      apply List.any_eq_true.mpr
      refine ⟨(rightName, leftFields), ?_, ?_⟩
      · simpa [leftGroups, source, collectRuntimeFieldGroups] using hleftGroup
      cases hleftFieldsEq : leftFields with
      | nil =>
          have hleftGroupReady := hleftGroupsReady rightName leftFields (by
            simpa [source] using hleftGroup)
          exact False.elim (hleftGroupReady.1 hleftFieldsEq)
      | cons leftHead leftRest =>
          cases hrightFieldsEq : rightFields with
          | nil =>
              have hrightGroupReady := hrightGroupsReady rightName rightFields (by
                simpa [source] using hrightGroup')
              exact False.elim (hrightGroupReady.1 hrightFieldsEq)
          | cons rightHead rightRest =>
              have hleftHead : leftHead ∈ leftFields := by simp [hleftFieldsEq]
              have hrightHead : rightHead ∈ rightFields := by simp [hrightFieldsEq]
              rcases hfields rightHead hrightHead with
                ⟨leftWitness, hleftWitness, hwitness⟩
              have hleftGroupReady := hleftGroupsReady rightName leftFields (by
                simpa [source] using hleftGroup)
              have hrightGroupReady := hrightGroupsReady rightName rightFields (by
                simpa [source] using hrightGroup')
              rcases hleftGroupReady.2.2.1 leftHead leftWitness hleftHead
                  hleftWitness with
                ⟨hleftParent, hleftFieldName, hleftArguments⟩
              have hparent : leftHead.parentType = rightHead.parentType :=
                hleftParent.trans hwitness.parentType
              have hfieldName : leftHead.fieldName = rightHead.fieldName :=
                hleftFieldName.trans hwitness.fieldName
              have harguments : Argument.argumentsEquivalent leftHead.arguments
                  rightHead.arguments :=
                argumentsEquivalent_trans hleftArguments hwitness.arguments
              simp only [beq_self_eq_true, Bool.true_and, Bool.and_eq_true]
              refine ⟨⟨⟨beq_iff_eq.mpr hparent, beq_iff_eq.mpr hfieldName⟩,
                (argumentsSyntacticallyEquivalentBool_iff _ _).mpr harguments⟩, ?_⟩
              rcases hrightGroupReady.2.1 rightHead hrightHead with
                ⟨definition, hlookup, _hchildReady⟩
              rw [hlookup]
              cases hcomposite : definition.outputType.isCompositeBool schema with
              | false => simp [hcomposite]
              | true =>
                  simp only [hcomposite, if_true, List.all_eq_true]
                  intro childRuntimeType hchildRuntime
                  have hchildObject : schema.objectType childRuntimeType :=
                    SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects hschema
                      definition.outputType.namedType childRuntimeType hchildRuntime
                  have hincludes : schema.typeIncludesObjectBool
                      definition.outputType.namedType childRuntimeType = true :=
                    List.contains_iff_mem.mpr hchildRuntime
                  have hleftWitnessLookup : schema.lookupField leftWitness.parentType
                      leftWitness.fieldName = some definition := by
                    simpa [hwitness.parentType, hwitness.fieldName] using hlookup
                  have hleftCompletion : completionFieldsSemanticsReady schema
                      definition.outputType leftFields :=
                    ⟨hleftGroupReady, leftWitness, definition, hleftWitness,
                      hleftWitnessLookup, rfl⟩
                  have hrightCompletion : completionFieldsSemanticsReady schema
                      definition.outputType rightFields :=
                    ⟨hrightGroupReady, rightHead, definition, hrightHead, hlookup, rfl⟩
                  have hleftChildReady :=
                    completionFieldsSemanticsReady_merged_semantics hleftCompletion
                      hincludes
                  have hrightChildReady :=
                    completionFieldsSemanticsReady_merged_semantics hrightCompletion
                      hincludes
                  have hleftChildMerge :=
                    completionFieldsSemanticsReady_merged_canMerge hleftCompletion
                      childRuntimeType
                  have hrightChildMerge :=
                    completionFieldsSemanticsReady_merged_canMerge hrightCompletion
                      childRuntimeType
                  have hchildSyntax := syntacticallyIncludedMergedSelectionSets hfields
                  have hrightFieldsDepth : ExecutableFieldsResponseDepthBound rightFields
                      (childFuel + 1) := by
                    intro field hfield
                    have hbound := collectFields_responseDepth_bound schema variableValues
                      parentType source right
                    have hfieldFlat : field ∈
                        (collectFields schema variableValues parentType source right).flatMap
                          Prod.snd :=
                      List.mem_flatMap.mpr ⟨(rightName, rightFields), hrightGroup', hfield⟩
                    exact Nat.le_trans (hbound field hfieldFlat) hdepth
                  have hchildDepth : selectionSetResponseDepth
                      (executableFieldsMergedSelectionSet rightFields) ≤ childFuel := by
                    exact selectionSetResponseDepth_flatMap_le rightFields childFuel
                      hrightFieldsDepth
                  have hresult := ih childRuntimeType
                    (executableFieldsMergedSelectionSet leftFields)
                    (executableFieldsMergedSelectionSet rightFields) hchildObject
                    (by simpa [executableFieldsMergedSelectionSet_eq_mergedFieldSelectionSet]
                      using hleftChildReady)
                    (by simpa [executableFieldsMergedSelectionSet_eq_mergedFieldSelectionSet]
                      using hleftChildMerge)
                    (by simpa [executableFieldsMergedSelectionSet_eq_mergedFieldSelectionSet]
                      using hrightChildReady)
                    (by simpa [executableFieldsMergedSelectionSet_eq_mergedFieldSelectionSet]
                      using hrightChildMerge)
                    hchildDepth hchildSyntax
                  simpa [hleftFieldsEq, hrightFieldsEq] using hresult

end QueryInclusion
end GraphQL
