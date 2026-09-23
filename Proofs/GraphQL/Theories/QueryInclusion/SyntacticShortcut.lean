import Proofs.GraphQL.Theories.QueryInclusion.RegionSearch
import Proofs.GraphQL.List

/-! Soundness of the conservative syntax-only query-inclusion shortcut. -/

namespace GraphQL
namespace QueryInclusion

open Execution
open Execution.FieldGroups
open GraphQL.ConditionTree

structure ExecutableFieldSyntacticallyIncludes (left right : ExecutableField) : Prop where
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

theorem withoutTransparentFragments_eq_flatMap
    (schema : Schema) (possibleTypes : List Name) (selectionSet : List Selection)
    : withoutTransparentFragments schema possibleTypes selectionSet
      = selectionSet.flatMap
          fun selection =>
            match selection with
            | .inlineFragment typeCondition directives body =>
                if fragmentTransparentForPossibleTypesBool schema possibleTypes
                    typeCondition directives then
                  withoutTransparentFragments schema possibleTypes body
                else
                  [.inlineFragment typeCondition directives body]
            | selection => [selection] := by
  induction selectionSet with
  | nil => simp [withoutTransparentFragments]
  | cons selection rest ih =>
      cases selection <;>
        simp [withoutTransparentFragments, ih]

theorem selectionSetBoundarySyntacticInclusionShortcutBool_of_perm
    {schema : Schema} {possibleTypes : List Name} {fuel : Nat}
    {left reorderedLeft right reorderedRight : List Selection}
    (hleft : left.Perm reorderedLeft) (hright : right.Perm reorderedRight)
    (hcheck
      : selectionSetBoundarySyntacticInclusionShortcutBool schema fuel
          possibleTypes left right
        = true)
    : selectionSetBoundarySyntacticInclusionShortcutBool schema fuel
        possibleTypes reorderedLeft reorderedRight
      = true := by
  simp only [selectionSetBoundarySyntacticInclusionShortcutBool,
    Bool.and_eq_true, decide_eq_true_iff] at hcheck ⊢
  refine ⟨by simpa [selectionSetResponseDepth_eq_of_perm hright] using hcheck.1, ?_⟩
  have hleftFlattened : (withoutTransparentFragments schema possibleTypes left).Perm
      (withoutTransparentFragments schema possibleTypes reorderedLeft) := by
    rw [withoutTransparentFragments_eq_flatMap,
      withoutTransparentFragments_eq_flatMap]
    exact hleft.flatMap _
  have hrightFlattened : (withoutTransparentFragments schema possibleTypes right).Perm
      (withoutTransparentFragments schema possibleTypes reorderedRight) := by
    rw [withoutTransparentFragments_eq_flatMap,
      withoutTransparentFragments_eq_flatMap]
    exact hright.flatMap _
  unfold selectionSetSyntacticallyIncludesAtBoundaryBool at hcheck ⊢
  rw [← selectionSetSyntacticallyIncludesBool_eq_of_perm hleftFlattened
    hrightFlattened]
  exact hcheck.2

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
      : ∀ rightEntry,
          rightEntry ∈ collectFlatSelection schema variableValues parentType source right
          -> ∃ leftEntry,
              leftEntry
                ∈ collectFlatSelection schema variableValues parentType source left
              ∧ leftEntry.1 = rightEntry.1
              ∧ ExecutableFieldSyntacticallyIncludes leftEntry.2 rightEntry.2 := by
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
            intro rightEntry hrightEntry
            cases hallows
                  : selectionDirectivesAllowBool variableValues leftDirectives with
            | false =>
                simp [collectFlatSelection, hallows] at hrightEntry
            | true =>
                simp only [collectFlatSelection, hallows, ite_true, List.mem_singleton]
                  at hrightEntry ⊢
                subst rightEntry
                refine ⟨_, rfl, rfl, ?_⟩
                exact {
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
                    simpa [collectFlatSelection, hallows]
                      using collectFlatFields_syntactically_includes schema variableValues
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
                        simpa [collectFlatSelection, hallows, happlies]
                          using collectFlatFields_syntactically_includes schema
                            variableValues parentType source leftSelectionSet
                            rightSelectionSet hselectionSet
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
      : ∀ rightEntry,
          rightEntry ∈ collectFlatFields schema variableValues parentType source right
          -> ∃ leftEntry,
              leftEntry ∈ collectFlatFields schema variableValues parentType source left
              ∧ leftEntry.1 = rightEntry.1
              ∧ ExecutableFieldSyntacticallyIncludes leftEntry.2 rightEntry.2 := by
    intro rightEntry hrightEntry
    rw [collectFlatFields_eq_flatMap_collectFlatSelection] at hrightEntry ⊢
    rcases List.mem_flatMap.mp hrightEntry with
      ⟨rightSelection, hrightSelection, hrightEntry⟩
    rcases (selectionSetSyntacticallyIncludesBool_iff left right).mp hsyntax
        rightSelection hrightSelection with
      ⟨leftSelection, hleftSelection, hselection⟩
    rcases collectFlatSelection_syntactically_includes schema variableValues
        parentType source leftSelection rightSelection hselection rightEntry hrightEntry with
      ⟨leftEntry, hleftEntry, hname, hincludes⟩
    exact ⟨leftEntry, List.mem_flatMap.mpr
      ⟨leftSelection, hleftSelection, hleftEntry⟩, hname, hincludes⟩
  termination_by 2 * SelectionSet.size right + 1
  decreasing_by
    all_goals
      have hle := selection_size_le_selectionSet_size_of_mem hrightSelection
      omega
end

private theorem collectFlatFields_append_local (schema : Schema)
    (variableValues : VariableValues) (parentType runtimeType : Name)
    (left right : List Selection)
    : collectFlatFields schema variableValues parentType
        (ResolverValue.object runtimeType PUnit.unit) (left ++ right)
      = collectFlatFields schema variableValues parentType
          (ResolverValue.object runtimeType PUnit.unit) left
        ++ collectFlatFields schema variableValues parentType
            (ResolverValue.object runtimeType PUnit.unit) right := by
  induction left with
  | nil => rfl
  | cons selection rest ih =>
      simp [collectFlatFields, ih, List.append_assoc]

private theorem transparentFragment_applies
    (schema : Schema) (possibleTypes : List Name) (runtimeType : Name)
    (typeCondition : Option Name) (directives : List DirectiveApplication)
    (htransparent
      : fragmentTransparentForPossibleTypesBool schema possibleTypes
          typeCondition directives
        = true)
    (hruntime : runtimeType ∈ possibleTypes)
    : directives = []
      ∧ ∀ condition,
          typeCondition = some condition
          -> schema.typeIncludesObjectBool condition runtimeType = true := by
  simp only [fragmentTransparentForPossibleTypesBool, Bool.and_eq_true] at htransparent
  have hdirectives : directives = [] := List.isEmpty_iff.mp htransparent.1
  refine ⟨hdirectives, ?_⟩
  intro condition hcondition
  subst typeCondition
  simp only [Bool.and_eq_true] at htransparent
  exact (List.all_eq_true.mp htransparent.2.2) runtimeType hruntime

theorem collectFlatFields_withoutTransparentFragments
    (schema : Schema) (possibleTypes : List Name) (variableValues : VariableValues)
    (parentType runtimeType : Name) (selectionSet : List Selection)
    (hruntime : runtimeType ∈ possibleTypes)
    : collectFlatFields schema variableValues parentType
        (ResolverValue.object runtimeType PUnit.unit)
        (withoutTransparentFragments schema possibleTypes selectionSet)
      = collectFlatFields schema variableValues parentType
          (ResolverValue.object runtimeType PUnit.unit) selectionSet := by
  cases selectionSet with
  | nil => simp [withoutTransparentFragments, collectFlatFields]
  | cons selection rest =>
      have hrest := collectFlatFields_withoutTransparentFragments schema possibleTypes
        variableValues parentType runtimeType rest hruntime
      cases selection with
      | field responseName fieldName arguments directives child =>
          simpa [withoutTransparentFragments, collectFlatFields]
            using congrArg
              (collectFlatSelection schema variableValues parentType
                  (ResolverValue.object runtimeType PUnit.unit)
                  (.field responseName fieldName arguments directives child)
                ++ ·)
              hrest
      | inlineFragment typeCondition directives body =>
          by_cases htransparent :
            fragmentTransparentForPossibleTypesBool schema possibleTypes
              typeCondition directives
            = true
          · have hbody := collectFlatFields_withoutTransparentFragments schema possibleTypes
              variableValues parentType runtimeType body hruntime
            rcases transparentFragment_applies schema possibleTypes runtimeType
                typeCondition directives htransparent hruntime with
              ⟨hdirectives, happlies⟩
            subst directives
            cases typeCondition with
            | none =>
                simp [withoutTransparentFragments, htransparent,
                  collectFlatFields_append_local, collectFlatFields,
                  collectFlatSelection, hbody, hrest,
                  selectionDirectivesAllowBool]
            | some condition =>
                have happly := happlies condition rfl
                simp [withoutTransparentFragments, htransparent,
                  collectFlatFields_append_local, collectFlatFields,
                  collectFlatSelection, hbody, hrest,
                  selectionDirectivesAllowBool, doesFragmentTypeApplyBool,
                  runtimeObjectType?, happly]
          · simp [withoutTransparentFragments, htransparent,
              collectFlatFields, hrest]
termination_by SelectionSet.size selectionSet
decreasing_by
  all_goals simp only [SelectionSet.size, Selection.size]
  all_goals first | omega | (cases selection <;> simp [Selection.size] <;> omega)

theorem collectFields_syntactically_includes
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectRef)
    (left right : List Selection)
    (hsyntax : selectionSetSyntacticallyIncludesBool left right = true)
    : ∀ rightEntry,
        rightEntry
          ∈ ConditionTree.flattenExecutableFieldGroups
              (collectFields schema variableValues parentType source right)
        -> ∃ leftEntry,
            leftEntry
              ∈ ConditionTree.flattenExecutableFieldGroups
                  (collectFields schema variableValues parentType source left)
            ∧ leftEntry.1 = rightEntry.1
            ∧ ExecutableFieldSyntacticallyIncludes leftEntry.2 rightEntry.2 := by
  intro rightEntry hrightEntry
  have hrightFlat : rightEntry ∈
      collectFlatFields schema variableValues parentType source right :=
    (collectFlatFields_perm_flatten_collectFields schema variableValues parentType
      source right).mem_iff.mpr hrightEntry
  rcases collectFlatFields_syntactically_includes schema variableValues parentType
      source left right hsyntax rightEntry hrightFlat with
    ⟨leftEntry, hleftFlat, hname, hincludes⟩
  exact ⟨leftEntry,
    (collectFlatFields_perm_flatten_collectFields schema variableValues parentType
      source left).mem_iff.mp hleftFlat,
    hname, hincludes⟩

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

theorem collectFields_included_group_of_cover
    (fieldRelation : ExecutableField -> ExecutableField -> Prop)
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectRef)
    (left right : List Selection)
    (hcover
      : ∀ rightEntry,
          rightEntry
            ∈ ConditionTree.flattenExecutableFieldGroups
                (collectFields schema variableValues parentType source right)
          -> ∃ leftEntry,
              leftEntry
                ∈ ConditionTree.flattenExecutableFieldGroups
                    (collectFields schema variableValues parentType source left)
              ∧ leftEntry.1 = rightEntry.1
              ∧ fieldRelation leftEntry.2 rightEntry.2)
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
                leftField ∈ leftFields ∧ fieldRelation leftField rightField := by
  let leftGroups := collectFields schema variableValues parentType source left
  let rightGroups := collectFields schema variableValues parentType source right
  have hrightWellFormed :=
    NormalForm.GroundTypeNormalization.collectFields_wellFormed schema variableValues
      parentType source right
  have hleftKeysNodup :=
    (executableGroupNamesNodup_iff_map_fst_nodup leftGroups).mp
      (NormalForm.collectFields_namesNodup schema variableValues parentType source left)
  have hrightNonempty := hrightWellFormed (rightName, rightFields) hrightGroup
  cases hrightFieldsEq : rightFields with
  | nil => exact False.elim (hrightNonempty hrightFieldsEq)
  | cons rightHead rightRest =>
      have hrightHead : rightHead ∈ rightFields := by simp [hrightFieldsEq]
      have hrightHeadFlat : (rightName, rightHead) ∈
          ConditionTree.flattenExecutableFieldGroups rightGroups :=
        (mem_flattenExecutableFieldGroups_iff rightGroups
          (rightName, rightHead)).mpr ⟨rightFields, hrightGroup, hrightHead⟩
      rcases hcover (rightName, rightHead) hrightHeadFlat with
        ⟨⟨leftName, leftWitness⟩, hleftWitnessFlat, hleftName, hwitness⟩
      rcases (mem_flattenExecutableFieldGroups_iff leftGroups
          (leftName, leftWitness)).mp
          hleftWitnessFlat with
        ⟨leftFields, hleftGroup, hleftWitness⟩
      refine ⟨leftFields, ?_, ?_⟩
      · rw [hleftName] at hleftGroup
        simpa [leftGroups] using hleftGroup
      intro rightField hrightField
      have hrightFieldOriginal : rightField ∈ rightFields := by
        simpa [hrightFieldsEq] using hrightField
      have hrightFieldFlat : (rightName, rightField) ∈
          ConditionTree.flattenExecutableFieldGroups rightGroups :=
        (mem_flattenExecutableFieldGroups_iff rightGroups
          (rightName, rightField)).mpr
          ⟨rightFields, hrightGroup, hrightFieldOriginal⟩
      rcases hcover (rightName, rightField) hrightFieldFlat with
        ⟨⟨candidateName, leftField⟩, hleftFieldFlat, hcandidateName,
          hincludes⟩
      rcases (mem_flattenExecutableFieldGroups_iff leftGroups
          (candidateName, leftField)).mp
          hleftFieldFlat with
        ⟨candidateFields, hcandidateGroup, hcandidateField⟩
      have hcandidateName' : candidateName = leftName :=
        hcandidateName.trans hleftName.symm
      have hgroupEq : (candidateName, candidateFields) = (leftName, leftFields) :=
        pair_eq_of_map_fst_nodup hleftKeysNodup hcandidateGroup hleftGroup
          hcandidateName'
      injection hgroupEq with _ hfieldsEq
      subst candidateFields
      exact ⟨leftField, hcandidateField, hincludes⟩

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
  exact collectFields_included_group_of_cover ExecutableFieldSyntacticallyIncludes
    schema variableValues parentType source
    left right (collectFields_syntactically_includes schema variableValues parentType
      source left right hsyntax) rightName rightFields hrightGroup

private theorem collectFields_possibleTypes_syntactically_includes
    (schema : Schema) (possibleTypes : List Name) (variableValues : VariableValues)
    (parentType runtimeType : Name) (left right : List Selection)
    (hruntime : runtimeType ∈ possibleTypes)
    (hsyntax
      : selectionSetSyntacticallyIncludesAtBoundaryBool schema possibleTypes left right
        = true)
    : ∀ rightEntry,
        rightEntry
          ∈ ConditionTree.flattenExecutableFieldGroups
              (collectFields schema variableValues parentType
                (ResolverValue.object runtimeType PUnit.unit) right)
        -> ∃ leftEntry,
            leftEntry
              ∈ ConditionTree.flattenExecutableFieldGroups
                  (collectFields schema variableValues parentType
                    (ResolverValue.object runtimeType PUnit.unit) left)
            ∧ leftEntry.1 = rightEntry.1
            ∧ ExecutableFieldSyntacticallyIncludes leftEntry.2 rightEntry.2 := by
  intro rightEntry hrightEntry
  have hrightFlat :=
    (collectFlatFields_perm_flatten_collectFields schema variableValues parentType
      (ResolverValue.object runtimeType PUnit.unit) right).mem_iff.mpr hrightEntry
  have hrightNormalized : rightEntry ∈ collectFlatFields schema variableValues
      parentType (ResolverValue.object runtimeType PUnit.unit)
        (withoutTransparentFragments schema possibleTypes right) := by
    rw [collectFlatFields_withoutTransparentFragments schema possibleTypes variableValues
      parentType runtimeType right hruntime]
    exact hrightFlat
  rcases collectFlatFields_syntactically_includes schema variableValues parentType
      (ResolverValue.object runtimeType PUnit.unit)
      (withoutTransparentFragments schema possibleTypes left)
      (withoutTransparentFragments schema possibleTypes right)
      hsyntax rightEntry hrightNormalized with
    ⟨leftEntry, hleftNormalized, hname, hincludes⟩
  have hleftFlat : leftEntry ∈ collectFlatFields schema variableValues parentType
      (ResolverValue.object runtimeType PUnit.unit) left := by
    rw [← collectFlatFields_withoutTransparentFragments schema possibleTypes variableValues
      parentType runtimeType left hruntime]
    exact hleftNormalized
  exact ⟨leftEntry,
    (collectFlatFields_perm_flatten_collectFields schema variableValues parentType
      (ResolverValue.object runtimeType PUnit.unit) left).mem_iff.mp hleftFlat,
    hname, hincludes⟩

theorem selectionSetFieldCover_sound
    (schema : Schema) (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (variableValues : VariableValues)
    (fieldRelation : Name -> ExecutableField -> ExecutableField -> Prop)
    (hidentity
      : ∀ parentType leftField rightField,
          fieldRelation parentType leftField rightField
          -> leftField.fieldName = rightField.fieldName
              ∧ Argument.argumentsEquivalent leftField.arguments rightField.arguments)
    (hdescend
      : ∀ parentType childRuntimeType definition
          (leftFields rightFields : List ExecutableField),
          (∀ rightField,
            rightField ∈ rightFields
            -> ∃ leftField,
                leftField ∈ leftFields ∧ fieldRelation parentType leftField rightField)
          -> (∀ rightField,
                rightField ∈ rightFields
                -> schema.lookupField parentType rightField.fieldName = some definition)
          -> childRuntimeType ∈ schema.getPossibleTypes definition.outputType.namedType
          -> ∀ rightName childRightFields,
              (rightName, childRightFields)
                ∈ collectFields schema variableValues
                    childRuntimeType (ResolverValue.object childRuntimeType PUnit.unit)
                    (executableFieldsMergedSelectionSet rightFields)
              -> ∃ childLeftFields,
                  (rightName, childLeftFields)
                    ∈ collectFields schema variableValues childRuntimeType
                        (ResolverValue.object childRuntimeType PUnit.unit)
                        (executableFieldsMergedSelectionSet leftFields)
                  ∧ ∀ childRightField,
                      childRightField ∈ childRightFields
                      -> ∃ childLeftField,
                          childLeftField ∈ childLeftFields
                          ∧ fieldRelation childRuntimeType childLeftField childRightField)
    (fuel : Nat) (parentType : Name)
    (left right : List Selection)
    (hparentObject : schema.objectType parentType)
    (hleftReady : NormalForm.selectionSetSemanticsReady schema parentType left)
    (hleftMerge : FieldMerge.fieldsInSetCanMerge schema parentType left)
    (hrightReady : NormalForm.selectionSetSemanticsReady schema parentType right)
    (hrightMerge : FieldMerge.fieldsInSetCanMerge schema parentType right)
    (hdepth : selectionSetResponseDepth right ≤ fuel)
    (hcover
      : ∀ rightName rightFields,
          (rightName, rightFields)
            ∈ collectFields schema variableValues parentType
                (ResolverValue.object parentType PUnit.unit) right
          -> ∃ leftFields,
              (rightName, leftFields)
                ∈ collectFields schema variableValues parentType
                    (ResolverValue.object parentType PUnit.unit) left
              ∧ ∀ rightField,
                  rightField ∈ rightFields
                  -> ∃ leftField,
                      leftField ∈ leftFields
                      ∧ fieldRelation parentType leftField rightField)
    : selectionSetIncludesBoolWithFuel schema fuel parentType variableValues left right
      = true := by
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
          have hgroupReady :=
            hgroupsReady responseName fields
              (by
                simpa [rightGroups, collectRuntimeFieldGroups]
                  using show (responseName, fields) ∈ rightGroups by simp [hgroups])
          cases hfields : fields with
          | nil => exact False.elim (hgroupReady.1 hfields)
          | cons field fields =>
              have hbound := collectFields_responseDepth_bound schema variableValues
                parentType (ResolverValue.object parentType PUnit.unit) right
              have hgroupMem : (responseName, field :: fields) ∈
                  collectFields schema variableValues parentType
                    (ResolverValue.object parentType PUnit.unit) right := by
                simpa [rightGroups, collectRuntimeFieldGroups]
                  using show (responseName, field :: fields) ∈ rightGroups by
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
      rcases hcover rightName rightFields hrightGroup' with
        ⟨leftFields, hleftGroup, hfields⟩
      apply List.any_eq_true.mpr
      refine ⟨(rightName, leftFields), ?_, ?_⟩
      · simpa [leftGroups, source, collectRuntimeFieldGroups] using hleftGroup
      cases hleftFieldsEq : leftFields with
      | nil =>
          have hleftGroupReady :=
            hleftGroupsReady rightName leftFields (by simpa [source] using hleftGroup)
          exact False.elim (hleftGroupReady.1 hleftFieldsEq)
      | cons leftHead leftRest =>
          cases hrightFieldsEq : rightFields with
          | nil =>
              have hrightGroupReady :=
                hrightGroupsReady rightName rightFields
                  (by simpa [source] using hrightGroup')
              exact False.elim (hrightGroupReady.1 hrightFieldsEq)
          | cons rightHead rightRest =>
              have hleftHead : leftHead ∈ leftFields := by simp [hleftFieldsEq]
              have hrightHead : rightHead ∈ rightFields := by simp [hrightFieldsEq]
              rcases hfields rightHead hrightHead with
                ⟨leftWitness, hleftWitness, hwitness⟩
              rcases hidentity parentType leftWitness rightHead hwitness with
                ⟨hwitnessName, hwitnessArguments⟩
              have hleftGroupReady :=
                hleftGroupsReady rightName leftFields (by simpa [source] using hleftGroup)
              have hrightGroupReady :=
                hrightGroupsReady rightName rightFields
                  (by simpa [source] using hrightGroup')
              rcases hleftGroupReady.2.2.1 leftHead leftWitness hleftHead
                  hleftWitness with
                ⟨hleftFieldName, hleftArguments⟩
              have hfieldName : leftHead.fieldName = rightHead.fieldName :=
                hleftFieldName.trans hwitnessName
              have harguments : Argument.argumentsEquivalent leftHead.arguments
                  rightHead.arguments :=
                argumentsEquivalent_trans hleftArguments hwitnessArguments
              simp only [beq_self_eq_true, Bool.true_and, Bool.and_eq_true]
              refine ⟨⟨beq_iff_eq.mpr hfieldName,
                (argumentsSyntacticallyEquivalentBool_iff _ _).mpr harguments⟩, ?_⟩
              rcases hrightGroupReady.2.1 rightHead hrightHead with
                ⟨definition, hlookup, _hchildReady⟩
              rw [hlookup]
              cases hcomposite : definition.outputType.isCompositeBool schema with
              | false => simp [hcomposite]
              | true =>
                  simp only [hcomposite, ite_true, List.all_eq_true]
                  intro childRuntimeType hchildRuntime
                  have hchildObject : schema.objectType childRuntimeType :=
                    SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects hschema
                      definition.outputType.namedType childRuntimeType hchildRuntime
                  have hincludes : schema.typeIncludesObjectBool
                      definition.outputType.namedType childRuntimeType = true :=
                    List.contains_iff_mem.mpr hchildRuntime
                  have hleftWitnessLookup : schema.lookupField parentType
                      leftWitness.fieldName = some definition := by
                    simpa [hwitnessName] using hlookup
                  have hleftCompletion : completionFieldsSemanticsReady schema
                      parentType definition.outputType leftFields :=
                    ⟨hleftGroupReady, leftWitness, definition, hleftWitness,
                      hleftWitnessLookup, rfl⟩
                  have hrightCompletion : completionFieldsSemanticsReady schema
                      parentType definition.outputType rightFields :=
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
                  have hlookupAll : ∀ rightField, rightField ∈ rightFields
                      -> schema.lookupField parentType rightField.fieldName
                        = some definition := by
                    intro rightField hrightField
                    rcases hrightGroupReady.2.2.1 rightHead rightField hrightHead
                        hrightField with ⟨hname, _⟩
                    simpa [← hname] using hlookup
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
                  have hresult :=
                    ih childRuntimeType
                      (executableFieldsMergedSelectionSet leftFields)
                      (executableFieldsMergedSelectionSet rightFields)
                      hchildObject
                      (by
                        simpa [
                          executableFieldsMergedSelectionSet_eq_mergedFieldSelectionSet]
                          using hleftChildReady)
                      (by
                        simpa [
                          executableFieldsMergedSelectionSet_eq_mergedFieldSelectionSet]
                          using hleftChildMerge)
                      (by
                        simpa [
                          executableFieldsMergedSelectionSet_eq_mergedFieldSelectionSet]
                          using hrightChildReady)
                      (by
                        simpa [
                          executableFieldsMergedSelectionSet_eq_mergedFieldSelectionSet]
                          using hrightChildMerge)
                      hchildDepth
                      (by
                        intro childRightName childRightFields hrightGroup
                        exact hdescend parentType childRuntimeType definition
                          leftFields rightFields hfields hlookupAll hchildRuntime
                          childRightName childRightFields hrightGroup)
                  simpa [hleftFieldsEq, hrightFieldsEq] using hresult

private theorem selectionSetSyntacticFieldCover_sound
    (schema : Schema) (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (fuel : Nat) (parentType : Name) (variableValues : VariableValues)
    (left right : List Selection)
    (hparentObject : schema.objectType parentType)
    (hleftReady : NormalForm.selectionSetSemanticsReady schema parentType left)
    (hleftMerge : FieldMerge.fieldsInSetCanMerge schema parentType left)
    (hrightReady : NormalForm.selectionSetSemanticsReady schema parentType right)
    (hrightMerge : FieldMerge.fieldsInSetCanMerge schema parentType right)
    (hdepth : selectionSetResponseDepth right ≤ fuel)
    (hcover
      : ∀ rightName rightFields,
          (rightName, rightFields)
            ∈ collectFields schema variableValues parentType
                (ResolverValue.object parentType PUnit.unit) right
          -> ∃ leftFields,
              (rightName, leftFields)
                ∈ collectFields schema variableValues parentType
                    (ResolverValue.object parentType PUnit.unit) left
              ∧ ∀ rightField,
                  rightField ∈ rightFields
                  -> ∃ leftField,
                      leftField ∈ leftFields
                      ∧ ExecutableFieldSyntacticallyIncludes leftField rightField)
    : selectionSetIncludesBoolWithFuel schema fuel parentType variableValues left right
      = true := by
  exact selectionSetFieldCover_sound schema hschema variableValues
    (fun _ => ExecutableFieldSyntacticallyIncludes)
    (by intro _ leftField rightField hwitness
        exact ⟨hwitness.fieldName, hwitness.arguments⟩)
    (by
      intro _ childRuntimeType _ leftFields rightFields hfields _ _
        childRightName childRightFields hrightGroup
      have hchildSyntax := syntacticallyIncludedMergedSelectionSets hfields
      exact collectFields_syntactically_included_group schema variableValues
        childRuntimeType (ResolverValue.object childRuntimeType PUnit.unit)
        (executableFieldsMergedSelectionSet leftFields)
        (executableFieldsMergedSelectionSet rightFields) hchildSyntax
        childRightName childRightFields hrightGroup)
    fuel parentType left right hparentObject hleftReady hleftMerge hrightReady
    hrightMerge hdepth hcover

theorem selectionSetBoundarySyntacticInclusionShortcutBool_sound
    (schema : Schema) (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (fuel : Nat) (possibleTypes : List Name) (parentType : Name)
    (variableValues : VariableValues) (left right : List Selection)
    (hparentInPossibleTypes : parentType ∈ possibleTypes)
    (hparentObject : schema.objectType parentType)
    (hleftReady : NormalForm.selectionSetSemanticsReady schema parentType left)
    (hleftMerge : FieldMerge.fieldsInSetCanMerge schema parentType left)
    (hrightReady : NormalForm.selectionSetSemanticsReady schema parentType right)
    (hrightMerge : FieldMerge.fieldsInSetCanMerge schema parentType right)
    (hcheck
      : selectionSetBoundarySyntacticInclusionShortcutBool schema fuel
          possibleTypes left right
        = true)
    : selectionSetIncludesBoolWithFuel schema fuel parentType variableValues left right
      = true := by
  simp only [selectionSetBoundarySyntacticInclusionShortcutBool, Bool.and_eq_true,
    decide_eq_true_iff] at hcheck
  rcases hcheck with ⟨hdepth, hsyntax⟩
  exact selectionSetSyntacticFieldCover_sound schema hschema fuel parentType
    variableValues left right hparentObject hleftReady hleftMerge hrightReady hrightMerge
    hdepth
    (by
      intro rightName rightFields hrightGroup
      exact collectFields_included_group_of_cover ExecutableFieldSyntacticallyIncludes
        schema variableValues parentType
        (ResolverValue.object parentType PUnit.unit) left right
        (collectFields_possibleTypes_syntactically_includes schema possibleTypes variableValues
          parentType parentType left right hparentInPossibleTypes hsyntax)
        rightName rightFields hrightGroup)

end QueryInclusion
end GraphQL
