import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.FocusedContextualSeparation
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.FocusedObjectChildLift

namespace GraphQL.NormalForm.GroundTypeNormalization

theorem focusedSelectionSetTargetChildSelectionSets_typenameFree
    (fieldName : Name) (leftArguments rightArguments : List Argument)
    {selections : List Selection} (hfree : selectionSetTypenameFree selections)
    : selectionSetTypenameFree
        (focusedSelectionSetTargetChildSelectionSets fieldName leftArguments
          rightArguments selections).flatten := by
  unfold selectionSetTypenameFree
  intro selection hmem
  rcases List.mem_flatten.mp hmem with ⟨children, hchild, hmem⟩
  rcases focusedSelectionSetTargetChildSelectionSets_mem hchild with
    ⟨responseName, arguments, directives, hfield⟩
  have hchildren := selectionSetTypenameFree_fieldChildren hfree hfield
  unfold selectionSetTypenameFree at hchildren
  exact hchildren selection hmem

theorem focusedSupportTargetChildSelectionSets_typenameFree
    (fieldName : Name) (leftArguments rightArguments : List Argument)
    {members : List (List Selection)} (hfree : selectionSetTypenameFree members.flatten)
    : selectionSetTypenameFree
        (focusedSupportTargetChildSelectionSets fieldName leftArguments rightArguments
          members).flatten := by
  induction members with
  | nil =>
      simpa [focusedSupportTargetChildSelectionSets] using selectionSetTypenameFree_nil
  | cons head tail ih =>
      simpa only [focusedSupportTargetChildSelectionSets, List.flatten_append]
        using selectionSetTypenameFree_append
          (focusedSelectionSetTargetChildSelectionSets_typenameFree fieldName
            leftArguments rightArguments
            (selectionSetTypenameFree_flatten_mem hfree (by simp)))
          (ih (selectionSetTypenameFree_append_right hfree))

theorem focusedObjectChildSupportSelectionSets_typenameFree (fieldName : Name)
    (leftArguments rightArguments : List Argument)
    {leftPref rightPref leftSuffix rightSuffix : List Selection}
    {support : List (List Selection)} (hlp : selectionSetTypenameFree leftPref)
    (hrp : selectionSetTypenameFree rightPref) (hls : selectionSetTypenameFree leftSuffix)
    (hrs : selectionSetTypenameFree rightSuffix)
    (hsupport : selectionSetTypenameFree support.flatten)
    : selectionSetTypenameFree
        (focusedObjectChildSupportSelectionSets fieldName leftArguments rightArguments
          leftPref rightPref leftSuffix rightSuffix support).flatten := by
  simp only [focusedObjectChildSupportSelectionSets, focusedSplitTargetChildSelectionSets,
    List.flatten_append]
  exact selectionSetTypenameFree_append
    (selectionSetTypenameFree_append
      (selectionSetTypenameFree_append
        (selectionSetTypenameFree_append
          (focusedSelectionSetTargetChildSelectionSets_typenameFree _ _ _ hlp)
          (focusedSelectionSetTargetChildSelectionSets_typenameFree _ _ _ hrp))
        (focusedSelectionSetTargetChildSelectionSets_typenameFree _ _ _ hls))
      (focusedSelectionSetTargetChildSelectionSets_typenameFree _ _ _ hrs))
    (focusedSupportTargetChildSelectionSets_typenameFree _ _ _ hsupport)

theorem selectionSetTargetInlineFragmentSelectionSets_typenameFree (condition : Name)
    {selections : List Selection} (hfree : selectionSetTypenameFree selections)
    : selectionSetTypenameFree
        (selectionSetTargetInlineFragmentSelectionSets condition selections).flatten := by
  unfold selectionSetTypenameFree
  intro selection hmem
  rcases List.mem_flatten.mp hmem with ⟨children, hchild, hmem⟩
  rcases selectionSetTargetInlineFragmentSelectionSets_mem hchild with ⟨directives, hfragment⟩
  have hchildren := selectionSetTypenameFree_fragmentChildren hfree hfragment
  unfold selectionSetTypenameFree at hchildren
  exact hchildren selection hmem

theorem supportTargetInlineFragmentSelectionSets_typenameFree
    (condition : Name) {members : List (List Selection)}
    (hfree : selectionSetTypenameFree members.flatten)
    : selectionSetTypenameFree
        (supportTargetInlineFragmentSelectionSets condition members).flatten := by
  induction members with
  | nil =>
      simpa [supportTargetInlineFragmentSelectionSets] using selectionSetTypenameFree_nil
  | cons head tail ih =>
      simpa only [supportTargetInlineFragmentSelectionSets, List.flatten_append]
        using selectionSetTypenameFree_append
          (selectionSetTargetInlineFragmentSelectionSets_typenameFree condition
            (selectionSetTypenameFree_flatten_mem hfree (by simp)))
          (ih (selectionSetTypenameFree_append_right hfree))

theorem abstractChildSupportSelectionSets_typenameFree (condition : Name)
    {leftPref rightPref leftSuffix rightSuffix : List Selection}
    {support : List (List Selection)} (hlp : selectionSetTypenameFree leftPref)
    (hrp : selectionSetTypenameFree rightPref) (hls : selectionSetTypenameFree leftSuffix)
    (hrs : selectionSetTypenameFree rightSuffix)
    (hsupport : selectionSetTypenameFree support.flatten)
    : selectionSetTypenameFree
        (abstractChildSupportSelectionSets condition leftPref rightPref leftSuffix
          rightSuffix support).flatten := by
  simp only [abstractChildSupportSelectionSets, splitTargetInlineFragmentSelectionSets,
    List.flatten_append]
  exact selectionSetTypenameFree_append
    (selectionSetTypenameFree_append
      (selectionSetTypenameFree_append
        (selectionSetTypenameFree_append
          (selectionSetTargetInlineFragmentSelectionSets_typenameFree _ hlp)
          (selectionSetTargetInlineFragmentSelectionSets_typenameFree _ hrp))
        (selectionSetTargetInlineFragmentSelectionSets_typenameFree _ hls))
      (selectionSetTargetInlineFragmentSelectionSets_typenameFree _ hrs))
    (supportTargetInlineFragmentSelectionSets_typenameFree _ hsupport)

end GraphQL.NormalForm.GroundTypeNormalization
