import Proofs.GraphQL.Theories.QueryInclusion.SyntacticShortcut

/-! Structural facts for syntactic inclusion across nested selection-set boundaries. -/

namespace GraphQL
namespace QueryInclusion

open Execution
open Execution.FieldGroups
open GraphQL.ConditionTree

def ExecutableFieldRecursiveSyntaxWitness (schema : Schema) (runtimeType : Name)
    (left right : ExecutableField)
    : Prop :=
  ∃ (possibleTypes : List Name) (budget : Nat),
    runtimeType ∈ possibleTypes
    ∧ left.fieldName = right.fieldName
    ∧ Argument.argumentsEquivalent left.arguments right.arguments
    ∧ selectionSetSyntacticallyIncludesRecursivelyAux schema budget
        (syntacticFieldChildPossibleTypes schema possibleTypes right.fieldName)
        left.selectionSet right.selectionSet
      = true

theorem syntacticFieldChildPossibleTypes_contains (schema : Schema)
    (possibleTypes : List Name) (parentType fieldName childType : Name)
    (definition : FieldDefinition)
    (hparent : parentType ∈ possibleTypes)
    (hlookup : schema.lookupField parentType fieldName = some definition)
    (hchild : childType ∈ schema.getPossibleTypes definition.outputType.namedType)
    : childType ∈ syntacticFieldChildPossibleTypes schema possibleTypes fieldName := by
  unfold syntacticFieldChildPossibleTypes
  exact List.mem_flatMap.mpr ⟨parentType, hparent, by simp [hlookup, hchild]⟩

theorem syntacticFragmentChildPossibleTypes_contains (schema : Schema)
    (possibleTypes : List Name) (parentType runtimeType : Name)
    (typeCondition : Option Name)
    (hparent : runtimeType ∈ possibleTypes)
    (happlicable
      : ∀ condition,
          typeCondition = some condition
          -> doesFragmentTypeApplyBool schema parentType
                (ResolverValue.object runtimeType PUnit.unit) condition
              = true)
    : runtimeType
      ∈ syntacticFragmentChildPossibleTypes schema possibleTypes typeCondition := by
  cases typeCondition with
  | none => exact hparent
  | some condition =>
      simp only [syntacticFragmentChildPossibleTypes, List.mem_filter]
      refine ⟨hparent, ?_⟩
      simpa [doesFragmentTypeApplyBool, runtimeObjectType?]
        using happlicable condition rfl

theorem selectionSetSyntacticallyIncludesRecursivelyAux_iff
    (schema : Schema) (budget : Nat) (possibleTypes : List Name)
    (left right : List Selection)
    : selectionSetSyntacticallyIncludesRecursivelyAux schema (budget + 1)
          possibleTypes left right
        = true
      ↔ ∀ rightSelection,
          rightSelection ∈ withoutTransparentFragments schema possibleTypes right
          -> ∃ leftSelection,
              leftSelection ∈ withoutTransparentFragments schema possibleTypes left
              ∧ syntacticSelectionIncludesWithChildCheckBool schema possibleTypes
                  (selectionSetSyntacticallyIncludesRecursivelyAux schema budget)
                  leftSelection rightSelection
                = true := by
  simp only [selectionSetSyntacticallyIncludesRecursivelyAux,
    List.all_eq_true, List.any_eq_true]

theorem selectionSetSyntacticallyIncludesRecursivelyAux_of_perm
    (schema : Schema) (budget : Nat) (possibleTypes : List Name)
    {left reorderedLeft right reorderedRight : List Selection}
    (hleft : left.Perm reorderedLeft) (hright : right.Perm reorderedRight)
    (hcheck
      : selectionSetSyntacticallyIncludesRecursivelyAux schema budget
          possibleTypes left right
        = true)
    : selectionSetSyntacticallyIncludesRecursivelyAux schema budget
        possibleTypes reorderedLeft reorderedRight
      = true := by
  cases budget with
  | zero => simp [selectionSetSyntacticallyIncludesRecursivelyAux] at hcheck
  | succ budget =>
      rw [selectionSetSyntacticallyIncludesRecursivelyAux_iff] at hcheck ⊢
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
      intro rightSelection hrightSelection
      rcases hcheck rightSelection (hrightFlattened.mem_iff.mpr hrightSelection) with
        ⟨leftSelection, hleftSelection, hselection⟩
      exact ⟨leftSelection, hleftFlattened.mem_iff.mp hleftSelection, hselection⟩

theorem selectionSet_size_eq_of_perm
    {left right : List Selection} (hperm : left.Perm right)
    : SelectionSet.size left = SelectionSet.size right := by
  induction hperm with
  | nil => rfl
  | cons selection _rest ih => simp [SelectionSet.size, ih]
  | swap first second rest => simp [SelectionSet.size, Nat.add_left_comm]
  | trans _ _ ihleft ihright => exact ihleft.trans ihright

theorem selectionSetRecursiveSyntacticInclusionShortcutBool_of_perm
    {schema : Schema} {possibleTypes : List Name} {responseFuel : Nat}
    {left reorderedLeft right reorderedRight : List Selection}
    (hleft : left.Perm reorderedLeft) (hright : right.Perm reorderedRight)
    (hcheck
      : selectionSetRecursiveSyntacticInclusionShortcutBool schema responseFuel
          possibleTypes left right
        = true)
    : selectionSetRecursiveSyntacticInclusionShortcutBool schema responseFuel
        possibleTypes reorderedLeft reorderedRight
      = true := by
  simp only [selectionSetRecursiveSyntacticInclusionShortcutBool,
    selectionSetSyntacticallyIncludesRecursivelyBool,
    Bool.and_eq_true, decide_eq_true_iff] at hcheck ⊢
  refine ⟨by simpa [selectionSetResponseDepth_eq_of_perm hright] using hcheck.1, ?_⟩
  rw [← selectionSet_size_eq_of_perm hright]
  exact selectionSetSyntacticallyIncludesRecursivelyAux_of_perm schema
    (SelectionSet.size right + 1) possibleTypes hleft hright hcheck.2

theorem selectionSetsMayNeedRecursiveSyntaxAux_eq_of_perm
    (budget : Nat) {left reorderedLeft right reorderedRight : List Selection}
    (hleft : left.Perm reorderedLeft) (hright : right.Perm reorderedRight)
    : selectionSetsMayNeedRecursiveSyntaxAux budget left right
      = selectionSetsMayNeedRecursiveSyntaxAux budget reorderedLeft
          reorderedRight := by
  cases budget with
  | zero => rfl
  | succ budget =>
      apply Bool.eq_iff_iff.mpr
      simp only [selectionSetsMayNeedRecursiveSyntaxAux,
        List.any_eq_true]
      constructor
      · rintro ⟨leftSelection, hleftSelection, rightSelection, hrightSelection,
          hpair⟩
        exact ⟨leftSelection, hleft.mem_iff.mp hleftSelection,
          rightSelection, hright.mem_iff.mp hrightSelection, hpair⟩
      · rintro ⟨leftSelection, hleftSelection, rightSelection, hrightSelection,
          hpair⟩
        exact ⟨leftSelection, hleft.mem_iff.mpr hleftSelection,
          rightSelection, hright.mem_iff.mpr hrightSelection, hpair⟩

theorem selectionSetsMayNeedRecursiveSyntaxBool_eq_of_perm
    {left reorderedLeft right reorderedRight : List Selection}
    (hleft : left.Perm reorderedLeft) (hright : right.Perm reorderedRight)
    : selectionSetsMayNeedRecursiveSyntaxBool left right
      = selectionSetsMayNeedRecursiveSyntaxBool reorderedLeft reorderedRight := by
  unfold selectionSetsMayNeedRecursiveSyntaxBool
  rw [← selectionSet_size_eq_of_perm hright]
  exact selectionSetsMayNeedRecursiveSyntaxAux_eq_of_perm
    (SelectionSet.size right + 1) hleft hright

theorem collectFlatFields_recursiveSyntax_cover
    (schema : Schema) (budget : Nat) (possibleTypes : List Name)
    (variableValues : VariableValues) (parentType runtimeType : Name)
    (left right : List Selection)
    (hruntime : runtimeType ∈ possibleTypes)
    (hsyntax
      : selectionSetSyntacticallyIncludesRecursivelyAux schema budget
          possibleTypes left right
        = true)
    : ∀ rightEntry,
        rightEntry
          ∈ collectFlatFields schema variableValues parentType
              (ResolverValue.object runtimeType PUnit.unit) right
        -> ∃ leftEntry,
            leftEntry
              ∈ collectFlatFields schema variableValues parentType
                  (ResolverValue.object runtimeType PUnit.unit) left
            ∧ leftEntry.1 = rightEntry.1
            ∧ ExecutableFieldRecursiveSyntaxWitness schema runtimeType
                leftEntry.2 rightEntry.2 := by
  induction budget generalizing possibleTypes left right with
  | zero => simp [selectionSetSyntacticallyIncludesRecursivelyAux] at hsyntax
  | succ childBudget ih =>
      intro rightEntry hrightEntry
      have hrightNormalized : rightEntry ∈ collectFlatFields schema variableValues
          parentType (ResolverValue.object runtimeType PUnit.unit)
            (withoutTransparentFragments schema possibleTypes right) := by
        rw [collectFlatFields_withoutTransparentFragments schema possibleTypes
          variableValues parentType runtimeType right hruntime]
        exact hrightEntry
      rw [collectFlatFields_eq_flatMap_collectFlatSelection] at hrightNormalized
      rcases List.mem_flatMap.mp hrightNormalized with
        ⟨rightSelection, hrightSelection, hrightField⟩
      rcases (selectionSetSyntacticallyIncludesRecursivelyAux_iff schema childBudget
          possibleTypes left right).mp hsyntax rightSelection hrightSelection with
        ⟨leftSelection, hleftSelection, hpair⟩
      have hmatched : ∃ leftEntry,
          leftEntry ∈ collectFlatSelection schema variableValues parentType
            (ResolverValue.object runtimeType PUnit.unit) leftSelection
          ∧ leftEntry.1 = rightEntry.1
          ∧ ExecutableFieldRecursiveSyntaxWitness schema runtimeType
              leftEntry.2 rightEntry.2 := by
        cases leftSelection with
        | field leftResponseName leftFieldName leftArguments leftDirectives leftChild =>
            cases rightSelection with
            | inlineFragment _ _ _ =>
                simp [syntacticSelectionIncludesWithChildCheckBool] at hpair
            | field rightResponseName rightFieldName rightArguments rightDirectives
                rightChild =>
                simp only [syntacticSelectionIncludesWithChildCheckBool,
                  Bool.and_eq_true] at hpair
                have hresponseName : leftResponseName = rightResponseName :=
                  beq_iff_eq.mp hpair.1.1.1.1
                have hfieldName : leftFieldName = rightFieldName :=
                  beq_iff_eq.mp hpair.1.1.1.2
                have harguments :=
                  (argumentsSyntacticallyEquivalentBool_iff _ _).mp hpair.1.1.2
                have hdirectives : leftDirectives = rightDirectives :=
                  Algorithms.directiveListEqBool_eq hpair.1.2
                subst rightResponseName
                subst rightFieldName
                subst rightDirectives
                cases hallows
                      : selectionDirectivesAllowBool variableValues leftDirectives with
                | false => simp [collectFlatSelection, hallows] at hrightField
                | true =>
                    simp only [collectFlatSelection, hallows, ite_true,
                      List.mem_singleton] at hrightField ⊢
                    subst rightEntry
                    refine ⟨_, rfl, rfl, ?_⟩
                    exact ⟨possibleTypes, childBudget, hruntime, rfl, harguments,
                      hpair.2⟩
        | inlineFragment leftCondition leftDirectives leftBody =>
            cases rightSelection with
            | field _ _ _ _ _ =>
                simp [syntacticSelectionIncludesWithChildCheckBool] at hpair
            | inlineFragment rightCondition rightDirectives rightBody =>
                simp only [syntacticSelectionIncludesWithChildCheckBool,
                  Bool.and_eq_true] at hpair
                have hcondition : leftCondition = rightCondition :=
                  beq_iff_eq.mp hpair.1.1
                have hdirectives : leftDirectives = rightDirectives :=
                  Algorithms.directiveListEqBool_eq hpair.1.2
                subst rightCondition
                subst rightDirectives
                cases hallows
                      : selectionDirectivesAllowBool variableValues leftDirectives with
                | false =>
                    cases leftCondition <;>
                      simp [collectFlatSelection, hallows] at hrightField
                | true =>
                    cases leftCondition with
                    | none =>
                        have hinner := ih
                          (syntacticFragmentChildPossibleTypes schema possibleTypes none)
                          leftBody rightBody hruntime hpair.2 rightEntry
                        have hrightBody : rightEntry ∈ collectFlatFields schema
                            variableValues parentType
                            (ResolverValue.object runtimeType PUnit.unit) rightBody := by
                          simpa [collectFlatSelection, hallows] using hrightField
                        simpa [collectFlatSelection, hallows] using hinner hrightBody
                    | some condition =>
                        cases happly
                              : doesFragmentTypeApplyBool schema parentType
                                  (ResolverValue.object runtimeType PUnit.unit)
                                  condition with
                        | false =>
                            simp [collectFlatSelection, hallows, happly] at hrightField
                        | true =>
                            have hchildRuntime : runtimeType ∈
                                syntacticFragmentChildPossibleTypes schema possibleTypes
                                  (some condition) :=
                              syntacticFragmentChildPossibleTypes_contains schema
                                possibleTypes parentType runtimeType (some condition)
                                hruntime (by intro candidate hc; cases hc; exact happly)
                            have hinner := ih
                              (syntacticFragmentChildPossibleTypes schema possibleTypes
                                (some condition)) leftBody rightBody hchildRuntime
                              hpair.2 rightEntry
                            have hrightBody : rightEntry ∈ collectFlatFields schema
                                variableValues parentType
                                (ResolverValue.object runtimeType PUnit.unit)
                                  rightBody := by
                              simpa [collectFlatSelection, hallows, happly]
                                using hrightField
                            simpa [collectFlatSelection, hallows, happly]
                              using hinner hrightBody
      rcases hmatched with ⟨leftEntry, hleftField, hname, hwitness⟩
      have hleftNormalized : leftEntry ∈ collectFlatFields schema variableValues
          parentType (ResolverValue.object runtimeType PUnit.unit)
            (withoutTransparentFragments schema possibleTypes left) := by
        rw [collectFlatFields_eq_flatMap_collectFlatSelection]
        exact List.mem_flatMap.mpr
          ⟨leftSelection, hleftSelection, hleftField⟩
      have hleftEntry : leftEntry ∈ collectFlatFields schema variableValues
          parentType (ResolverValue.object runtimeType PUnit.unit) left := by
        rw [← collectFlatFields_withoutTransparentFragments schema possibleTypes
          variableValues parentType runtimeType left hruntime]
        exact hleftNormalized
      exact ⟨leftEntry, hleftEntry, hname, hwitness⟩

theorem collectFields_recursiveSyntax_included_group
    (schema : Schema) (budget : Nat) (possibleTypes : List Name)
    (variableValues : VariableValues) (parentType runtimeType : Name)
    (left right : List Selection)
    (hruntime : runtimeType ∈ possibleTypes)
    (hsyntax
      : selectionSetSyntacticallyIncludesRecursivelyAux schema budget
          possibleTypes left right
        = true)
    (rightName : Name) (rightFields : List ExecutableField)
    (hrightGroup
      : (rightName, rightFields)
        ∈ collectFields schema variableValues
            parentType (ResolverValue.object runtimeType PUnit.unit) right)
    : ∃ leftFields,
        (rightName, leftFields)
          ∈ collectFields schema variableValues parentType
              (ResolverValue.object runtimeType PUnit.unit) left
        ∧ ∀ rightField,
            rightField ∈ rightFields
            -> ∃ leftField,
                leftField ∈ leftFields
                ∧ ExecutableFieldRecursiveSyntaxWitness schema runtimeType
                    leftField rightField := by
  apply collectFields_included_group_of_cover
    (ExecutableFieldRecursiveSyntaxWitness schema runtimeType) schema variableValues
    parentType (ResolverValue.object runtimeType PUnit.unit) left right
    (by
      intro rightEntry hrightFlat
      have hrightEntry :=
        (collectFlatFields_perm_flatten_collectFields schema variableValues
          parentType (ResolverValue.object runtimeType PUnit.unit) right).mem_iff.mpr
          hrightFlat
      rcases collectFlatFields_recursiveSyntax_cover schema budget possibleTypes
          variableValues parentType runtimeType left right hruntime hsyntax
          rightEntry hrightEntry with
        ⟨leftEntry, hleftEntry, hname, hwitness⟩
      exact ⟨leftEntry,
        (collectFlatFields_perm_flatten_collectFields schema variableValues
          parentType (ResolverValue.object runtimeType PUnit.unit) left).mem_iff.mp
          hleftEntry,
        hname, hwitness⟩)
    rightName rightFields hrightGroup

private theorem collectFlatFields_append_recursive (schema : Schema)
    (variableValues : VariableValues) (runtimeType : Name)
    (left right : List Selection)
    : collectFlatFields schema variableValues runtimeType
        (ResolverValue.object runtimeType PUnit.unit) (left ++ right)
      = collectFlatFields schema variableValues runtimeType
          (ResolverValue.object runtimeType PUnit.unit) left
        ++ collectFlatFields schema variableValues runtimeType
            (ResolverValue.object runtimeType PUnit.unit) right := by
  induction left with
  | nil => rfl
  | cons selection rest ih =>
      simp [collectFlatFields, ih, List.append_assoc]

private theorem collectFlatFields_mergedSelectionSet (schema : Schema)
    (variableValues : VariableValues) (runtimeType : Name)
    (fields : List ExecutableField)
    : collectFlatFields schema variableValues runtimeType
        (ResolverValue.object runtimeType PUnit.unit)
        (executableFieldsMergedSelectionSet fields)
      = fields.flatMap
          fun field =>
            collectFlatFields schema variableValues runtimeType
              (ResolverValue.object runtimeType PUnit.unit) field.selectionSet := by
  induction fields with
  | nil => rfl
  | cons field rest ih =>
      simp only [executableFieldsMergedSelectionSet, List.flatMap_cons,
        collectFlatFields_append_recursive]
      have ih' := ih
      simpa only [executableFieldsMergedSelectionSet]
        using congrArg
          (collectFlatFields schema variableValues runtimeType
              (ResolverValue.object runtimeType PUnit.unit) field.selectionSet
            ++ ·)
          ih'

theorem recursiveWitnessMergedChildFlatCover
    (schema : Schema) (variableValues : VariableValues)
    (parentType childRuntimeType : Name) (definition : FieldDefinition)
    (leftFields rightFields : List ExecutableField)
    (hfields
      : ∀ rightField,
          rightField ∈ rightFields
          -> ∃ leftField,
              leftField ∈ leftFields
              ∧ ExecutableFieldRecursiveSyntaxWitness schema parentType
                  leftField rightField)
    (hlookup
      : ∀ rightField,
          rightField ∈ rightFields
          -> schema.lookupField parentType rightField.fieldName = some definition)
    (hchildRuntime
      : childRuntimeType ∈ schema.getPossibleTypes definition.outputType.namedType)
    : ∀ rightEntry,
        rightEntry
          ∈ collectFlatFields schema variableValues childRuntimeType
              (ResolverValue.object childRuntimeType PUnit.unit)
              (executableFieldsMergedSelectionSet rightFields)
        -> ∃ leftEntry,
            leftEntry
              ∈ collectFlatFields schema variableValues childRuntimeType
                  (ResolverValue.object childRuntimeType PUnit.unit)
                  (executableFieldsMergedSelectionSet leftFields)
            ∧ leftEntry.1 = rightEntry.1
            ∧ ExecutableFieldRecursiveSyntaxWitness schema childRuntimeType
                leftEntry.2 rightEntry.2 := by
  intro rightEntry hrightEntry
  rw [collectFlatFields_mergedSelectionSet] at hrightEntry ⊢
  rcases List.mem_flatMap.mp hrightEntry with
    ⟨rightField, hrightField, hrightFieldEntry⟩
  rcases hfields rightField hrightField with
    ⟨leftField, hleftField, hfieldWitness⟩
  rcases hfieldWitness with
    ⟨possibleTypes, budget, hparent, hfieldName, _harguments, hsyntax⟩
  have hchildMember : childRuntimeType ∈
      syntacticFieldChildPossibleTypes schema possibleTypes rightField.fieldName :=
    syntacticFieldChildPossibleTypes_contains schema possibleTypes parentType
      rightField.fieldName childRuntimeType definition hparent
      (hlookup rightField hrightField) hchildRuntime
  rcases collectFlatFields_recursiveSyntax_cover schema budget
      (syntacticFieldChildPossibleTypes schema possibleTypes rightField.fieldName)
      variableValues childRuntimeType childRuntimeType leftField.selectionSet
      rightField.selectionSet hchildMember hsyntax rightEntry hrightFieldEntry with
    ⟨leftEntry, hleftEntry, hname, hwitness⟩
  exact ⟨leftEntry, List.mem_flatMap.mpr
    ⟨leftField, hleftField, hleftEntry⟩, hname, hwitness⟩

theorem recursiveWitnessMergedChildGroupCover
    (schema : Schema) (variableValues : VariableValues)
    (parentType childRuntimeType : Name) (definition : FieldDefinition)
    (leftFields rightFields : List ExecutableField)
    (hfields
      : ∀ rightField,
          rightField ∈ rightFields
          -> ∃ leftField,
              leftField ∈ leftFields
              ∧ ExecutableFieldRecursiveSyntaxWitness schema parentType
                  leftField rightField)
    (hlookup
      : ∀ rightField,
          rightField ∈ rightFields
          -> schema.lookupField parentType rightField.fieldName = some definition)
    (hchildRuntime
      : childRuntimeType ∈ schema.getPossibleTypes definition.outputType.namedType)
    (rightName : Name) (childRightFields : List ExecutableField)
    (hrightGroup
      : (rightName, childRightFields)
        ∈ collectFields schema
            variableValues childRuntimeType
            (ResolverValue.object childRuntimeType PUnit.unit)
            (executableFieldsMergedSelectionSet rightFields))
    : ∃ childLeftFields,
        (rightName, childLeftFields)
          ∈ collectFields schema variableValues
              childRuntimeType (ResolverValue.object childRuntimeType PUnit.unit)
              (executableFieldsMergedSelectionSet leftFields)
        ∧ ∀ rightField,
            rightField ∈ childRightFields
            -> ∃ leftField,
                leftField ∈ childLeftFields
                ∧ ExecutableFieldRecursiveSyntaxWitness schema childRuntimeType
                    leftField rightField := by
  exact collectFields_included_group_of_cover
    (ExecutableFieldRecursiveSyntaxWitness schema childRuntimeType) schema
    variableValues childRuntimeType
    (ResolverValue.object childRuntimeType PUnit.unit)
    (executableFieldsMergedSelectionSet leftFields)
    (executableFieldsMergedSelectionSet rightFields)
    (by
      intro rightEntry hrightFlat
      have hrightEntry :=
        (collectFlatFields_perm_flatten_collectFields schema variableValues
          childRuntimeType (ResolverValue.object childRuntimeType PUnit.unit)
          (executableFieldsMergedSelectionSet rightFields)).mem_iff.mpr hrightFlat
      rcases recursiveWitnessMergedChildFlatCover schema variableValues parentType
          childRuntimeType definition leftFields rightFields hfields hlookup
          hchildRuntime rightEntry hrightEntry with
        ⟨leftEntry, hleftEntry, hname, hwitness⟩
      exact ⟨leftEntry,
        (collectFlatFields_perm_flatten_collectFields schema variableValues
          childRuntimeType (ResolverValue.object childRuntimeType PUnit.unit)
          (executableFieldsMergedSelectionSet leftFields)).mem_iff.mp hleftEntry,
        hname, hwitness⟩)
    rightName childRightFields hrightGroup

theorem selectionSetRecursiveSyntacticInclusionShortcutBool_sound
    (schema : Schema) (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (responseFuel : Nat) (possibleTypes : List Name) (parentType : Name)
    (variableValues : VariableValues) (left right : List Selection)
    (hparentInPossibleTypes : parentType ∈ possibleTypes)
    (hparentObject : schema.objectType parentType)
    (hleftReady : NormalForm.selectionSetSemanticsReady schema parentType left)
    (hleftMerge : FieldMerge.fieldsInSetCanMerge schema parentType left)
    (hrightReady : NormalForm.selectionSetSemanticsReady schema parentType right)
    (hrightMerge : FieldMerge.fieldsInSetCanMerge schema parentType right)
    (hcheck
      : selectionSetRecursiveSyntacticInclusionShortcutBool schema responseFuel
          possibleTypes left right
        = true)
    : selectionSetIncludesBoolWithFuel schema responseFuel parentType variableValues
        left right
      = true := by
  simp only [selectionSetRecursiveSyntacticInclusionShortcutBool,
    selectionSetSyntacticallyIncludesRecursivelyBool,
    Bool.and_eq_true, decide_eq_true_iff] at hcheck
  rcases hcheck with ⟨hdepth, hsyntax⟩
  exact selectionSetFieldCover_sound schema hschema variableValues
    (ExecutableFieldRecursiveSyntaxWitness schema)
    (by
      intro _ leftField rightField hwitness
      rcases hwitness with ⟨_, _, _, hname, harguments, _⟩
      exact ⟨hname, harguments⟩)
    (by
      intro parentType childRuntimeType definition leftFields rightFields
        hfields hlookup hchildRuntime childRightName childRightFields hrightGroup
      exact recursiveWitnessMergedChildGroupCover schema variableValues parentType
        childRuntimeType definition leftFields rightFields hfields hlookup
        hchildRuntime childRightName childRightFields hrightGroup)
    responseFuel parentType left right hparentObject hleftReady hleftMerge
    hrightReady hrightMerge hdepth
    (by
      intro rightName rightFields hrightGroup
      exact collectFields_recursiveSyntax_included_group schema
        (SelectionSet.size right + 1) possibleTypes variableValues parentType
        parentType left right hparentInPossibleTypes hsyntax rightName rightFields
        hrightGroup)

theorem selectionSetSyntacticInclusionShortcutBool_of_perm
    {schema : Schema} {possibleTypes : List Name} {responseFuel : Nat}
    {left reorderedLeft right reorderedRight : List Selection}
    (hleft : left.Perm reorderedLeft) (hright : right.Perm reorderedRight)
    (hcheck
      : selectionSetSyntacticInclusionShortcutBool schema responseFuel
          possibleTypes left right
        = true)
    : selectionSetSyntacticInclusionShortcutBool schema responseFuel
        possibleTypes reorderedLeft reorderedRight
      = true := by
  simp only [selectionSetSyntacticInclusionShortcutBool,
    Bool.or_eq_true, Bool.and_eq_true] at hcheck ⊢
  rcases hcheck with hold | ⟨hguard, hrecursive⟩
  · exact Or.inl (selectionSetBoundarySyntacticInclusionShortcutBool_of_perm
      hleft hright hold)
  · refine Or.inr ⟨?_, selectionSetRecursiveSyntacticInclusionShortcutBool_of_perm
      hleft hright hrecursive⟩
    rw [← selectionSetsMayNeedRecursiveSyntaxBool_eq_of_perm hleft hright]
    exact hguard

theorem selectionSetSyntacticInclusionShortcutBool_sound
    (schema : Schema) (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (responseFuel : Nat) (possibleTypes : List Name) (parentType : Name)
    (variableValues : VariableValues) (left right : List Selection)
    (hparentInPossibleTypes : parentType ∈ possibleTypes)
    (hparentObject : schema.objectType parentType)
    (hleftReady : NormalForm.selectionSetSemanticsReady schema parentType left)
    (hleftMerge : FieldMerge.fieldsInSetCanMerge schema parentType left)
    (hrightReady : NormalForm.selectionSetSemanticsReady schema parentType right)
    (hrightMerge : FieldMerge.fieldsInSetCanMerge schema parentType right)
    (hcheck
      : selectionSetSyntacticInclusionShortcutBool schema responseFuel
          possibleTypes left right
        = true)
    : selectionSetIncludesBoolWithFuel schema responseFuel parentType variableValues
        left right
      = true := by
  simp only [selectionSetSyntacticInclusionShortcutBool,
    Bool.or_eq_true, Bool.and_eq_true] at hcheck
  rcases hcheck with hold | ⟨_hguard, hrecursive⟩
  · exact selectionSetBoundarySyntacticInclusionShortcutBool_sound schema
      hschema responseFuel possibleTypes parentType variableValues left right
      hparentInPossibleTypes hparentObject hleftReady hleftMerge hrightReady
      hrightMerge hold
  · exact selectionSetRecursiveSyntacticInclusionShortcutBool_sound schema hschema
      responseFuel possibleTypes parentType variableValues left right
      hparentInPossibleTypes hparentObject hleftReady hleftMerge hrightReady
      hrightMerge hrecursive

end QueryInclusion
end GraphQL
