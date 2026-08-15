import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Normality

/-!
Syntactic decomposition support for ground-type normal-form uniqueness.

This module is intentionally semantic-free: it only relates normal selection-set
syntax, directive-freedom, and the explicit equality-up-to-reordering relation.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

inductive NormalSelectionSetDiff (schema : Schema)
    : Name -> List Selection -> List Selection -> Prop where
  | objectLeftResponseName
    {parentType : Name} {left right : List Selection}
    {responseName fieldName : Name}
    {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet : List Selection}
    : objectTypeNameBool schema parentType = true
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ left
      -> responseName ∉ right.filterMap Selection.responseName?
      -> NormalSelectionSetDiff schema parentType left right
  | objectRightResponseName
    {parentType : Name} {left right : List Selection}
    {responseName fieldName : Name}
    {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet : List Selection}
    : objectTypeNameBool schema parentType = true
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ right
      -> responseName ∉ left.filterMap Selection.responseName?
      -> NormalSelectionSetDiff schema parentType left right
  | objectFieldName
    {parentType : Name} {left right : List Selection}
    {responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    : objectTypeNameBool schema parentType = true
      -> Selection.field responseName leftFieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName rightFieldName rightArguments rightDirectives
            rightChildSelectionSet
          ∈ right
      -> leftFieldName ≠ rightFieldName
      -> NormalSelectionSetDiff schema parentType left right
  | objectArguments
    {parentType : Name} {left right : List Selection}
    {responseName fieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    : objectTypeNameBool schema parentType = true
      -> Selection.field responseName fieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName fieldName rightArguments rightDirectives
            rightChildSelectionSet
          ∈ right
      -> ¬ Argument.argumentsEquivalent leftArguments rightArguments
      -> NormalSelectionSetDiff schema parentType left right
  | objectChild
    {parentType returnType : Name} {left right : List Selection}
    {responseName fieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    : objectTypeNameBool schema parentType = true
      -> schema.fieldReturnType? parentType fieldName = some returnType
      -> Selection.field responseName fieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName fieldName rightArguments rightDirectives
            rightChildSelectionSet
          ∈ right
      -> Argument.argumentsEquivalent leftArguments rightArguments
      -> NormalSelectionSetDiff schema returnType
          leftChildSelectionSet rightChildSelectionSet
      -> NormalSelectionSetDiff schema parentType left right
  | abstractLeftTypeCondition
    {parentType : Name} {left right : List Selection}
    {typeCondition : Name}
    {directives : List DirectiveApplication}
    {childSelectionSet : List Selection}
    : objectTypeNameBool schema parentType = false
      -> Selection.inlineFragment (some typeCondition) directives childSelectionSet ∈ left
      -> typeCondition ∉ right.filterMap inlineFragmentTypeCondition?
      -> NormalSelectionSetDiff schema parentType left right
  | abstractRightTypeCondition
    {parentType : Name} {left right : List Selection}
    {typeCondition : Name}
    {directives : List DirectiveApplication}
    {childSelectionSet : List Selection}
    : objectTypeNameBool schema parentType = false
      -> Selection.inlineFragment (some typeCondition) directives childSelectionSet
          ∈ right
      -> typeCondition ∉ left.filterMap inlineFragmentTypeCondition?
      -> NormalSelectionSetDiff schema parentType left right
  | abstractChild
    {parentType typeCondition : Name} {left right : List Selection}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    : objectTypeNameBool schema parentType = false
      -> Selection.inlineFragment (some typeCondition) leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.inlineFragment (some typeCondition) rightDirectives
            rightChildSelectionSet
          ∈ right
      -> NormalSelectionSetDiff schema typeCondition
          leftChildSelectionSet rightChildSelectionSet
      -> NormalSelectionSetDiff schema parentType left right

mutual
  theorem inputValue_structuralEquivalent_refl_forSyntaxDiff
      : ∀ value, InputValue.structuralEquivalent value value
    | .null => by simp [InputValue.structuralEquivalent]
    | .int _ => by simp [InputValue.structuralEquivalent]
    | .float _ => by simp [InputValue.structuralEquivalent]
    | .string _ => by simp [InputValue.structuralEquivalent]
    | .boolean _ => by simp [InputValue.structuralEquivalent]
    | .enum _ => by simp [InputValue.structuralEquivalent]
    | .variable _ => by simp [InputValue.structuralEquivalent]
    | .list values => by
        simp [InputValue.structuralEquivalent,
          inputValues_structuralEquivalent_refl_forSyntaxDiff values]
    | .object fields => by
        simp [InputValue.structuralEquivalent,
          inputObjectFields_structuralEquivalent_refl_forSyntaxDiff fields]

  theorem inputValues_structuralEquivalent_refl_forSyntaxDiff
      : ∀ values, InputValue.structuralValuesEquivalent values values
    | [] => by simp [InputValue.structuralValuesEquivalent]
    | value :: rest => by
        simp [InputValue.structuralValuesEquivalent,
          inputValue_structuralEquivalent_refl_forSyntaxDiff value,
          inputValues_structuralEquivalent_refl_forSyntaxDiff rest]

  theorem inputObjectFields_structuralEquivalent_refl_forSyntaxDiff
      : ∀ fields, InputValue.structuralObjectFieldsEquivalent fields fields
    | [] => by simp [InputValue.structuralObjectFieldsEquivalent]
    | (_name, value) :: rest => by
        simp [InputValue.structuralObjectFieldsEquivalent,
          inputValue_structuralEquivalent_refl_forSyntaxDiff value,
          inputObjectFields_structuralEquivalent_refl_forSyntaxDiff rest]
end

theorem inputValue_equivalent_refl_forSyntaxDiff (value : InputValue)
    : value.equivalent value := by
  exact inputValue_structuralEquivalent_refl_forSyntaxDiff value.canonical

theorem argument_equivalent_refl_forSyntaxDiff (argument : Argument)
    : argument.equivalent argument := by
  exact ⟨rfl, inputValue_equivalent_refl_forSyntaxDiff argument.value⟩

theorem argumentsEquivalent_refl_forSyntaxDiff (arguments : List Argument)
    : Argument.argumentsEquivalent arguments arguments := by
  constructor
  · intro argument hargument
    exact ⟨argument, hargument, argument_equivalent_refl_forSyntaxDiff argument⟩
  · intro argument hargument
    exact ⟨argument, hargument, argument_equivalent_refl_forSyntaxDiff argument⟩

theorem selectionSetNormal_responseNamesNodup
    {schema : Schema} {parentType : Name} {selectionSet : List Selection}
    : selectionSetNormal schema parentType selectionSet
      -> responseNamesNodup selectionSet := by
  intro hnormal
  unfold selectionSetNormal selectionSetNonRedundant at hnormal
  exact hnormal.2.1

theorem selectionSetNormal_inlineFragmentTypeConditionsNodup
    {schema : Schema} {parentType : Name} {selectionSet : List Selection}
    : selectionSetNormal schema parentType selectionSet
      -> inlineFragmentTypeConditionsNodup selectionSet := by
  intro hnormal
  unfold selectionSetNormal selectionSetNonRedundant at hnormal
  exact hnormal.2.2.1

theorem selectionSetNormal_allFields_of_object
    {schema : Schema} {parentType : Name} {selectionSet : List Selection}
    : selectionSetNormal schema parentType selectionSet
      -> objectTypeNameBool schema parentType = true
      -> selectionsAllFields selectionSet := by
  intro hnormal hobject
  unfold selectionSetNormal selectionSetGroundTyped at hnormal
  simpa [hobject] using hnormal.1.1

theorem selectionSet_field_mem_of_responseName_mem
    {selectionSet : List Selection} {responseName : Name}
    : selectionsAllFields selectionSet
      -> responseName ∈ selectionSet.filterMap Selection.responseName?
      -> ∃ fieldName arguments directives childSelectionSet,
          Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet := by
  intro hallFields hresponseName
  rcases List.mem_filterMap.mp hresponseName with
    ⟨selection, hselectionMem, hselectionName⟩
  have hfield : Selection.isField selection :=
    hallFields selection hselectionMem
  cases selection with
  | field candidateResponseName fieldName arguments directives
      childSelectionSet =>
      simp [Selection.responseName?] at hselectionName
      subst candidateResponseName
      exact ⟨fieldName, arguments, directives, childSelectionSet,
        hselectionMem⟩
  | inlineFragment typeCondition directives childSelectionSet =>
      simp [Selection.isField] at hfield

theorem selectionSetNormal_field_mem_of_responseName_mem
    {schema : Schema} {parentType : Name} {selectionSet : List Selection}
    {responseName : Name}
    : selectionSetNormal schema parentType selectionSet
      -> objectTypeNameBool schema parentType = true
      -> responseName ∈ selectionSet.filterMap Selection.responseName?
      -> ∃ fieldName arguments directives childSelectionSet,
          Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet := by
  intro hnormal hobject hresponseName
  exact
    selectionSet_field_mem_of_responseName_mem
      (selectionSetNormal_allFields_of_object hnormal hobject)
      hresponseName

theorem selectionSetNormal_allInlineFragments_of_abstract
    {schema : Schema} {parentType : Name} {selectionSet : List Selection}
    : selectionSetNormal schema parentType selectionSet
      -> objectTypeNameBool schema parentType = false
      -> selectionsAllInlineFragments selectionSet := by
  intro hnormal hobject
  unfold selectionSetNormal selectionSetGroundTyped at hnormal
  simpa [hobject] using hnormal.1.1

theorem selectionSetNormal_responseName_not_mem_of_abstract
    {schema : Schema} {parentType : Name} {selectionSet : List Selection}
    {responseName : Name}
    : selectionSetNormal schema parentType selectionSet
      -> objectTypeNameBool schema parentType = false
      -> responseName ∉ selectionSet.filterMap Selection.responseName? := by
  intro hnormal hobject hmem
  rcases List.mem_filterMap.mp hmem with
    ⟨selection, hselectionMem, hresponseName⟩
  have hinline : Selection.isInlineFragment selection :=
    selectionSetNormal_allInlineFragments_of_abstract hnormal hobject
      selection hselectionMem
  cases selection with
  | field responseName fieldName arguments directives childSelectionSet =>
      simp [Selection.isInlineFragment] at hinline
  | inlineFragment typeCondition directives childSelectionSet =>
      simp [Selection.responseName?] at hresponseName

theorem selectionsAllFields_tail {selection : Selection} {selectionSet : List Selection}
    : selectionsAllFields (selection :: selectionSet)
      -> selectionsAllFields selectionSet := by
  intro hallFields candidate hcandidate
  exact hallFields candidate (List.mem_cons_of_mem selection hcandidate)

theorem selectionsAllInlineFragments_tail
    {selection : Selection} {selectionSet : List Selection}
    : selectionsAllInlineFragments (selection :: selectionSet)
      -> selectionsAllInlineFragments selectionSet := by
  intro hallInlineFragments candidate hcandidate
  exact hallInlineFragments candidate
    (List.mem_cons_of_mem selection hcandidate)

theorem selectionSetGroundTyped_tail
    {schema : Schema} {parentType : Name}
    {selection : Selection} {selectionSet : List Selection}
    : selectionSetGroundTyped schema parentType (selection :: selectionSet)
      -> selectionSetGroundTyped schema parentType selectionSet := by
  intro hground
  unfold selectionSetGroundTyped at hground ⊢
  constructor
  · cases hobject : objectTypeNameBool schema parentType
    · exact selectionsAllInlineFragments_tail (by simpa [hobject] using hground.1)
    · exact selectionsAllFields_tail (by simpa [hobject] using hground.1)
  · intro candidate hcandidate
    exact hground.2 candidate (List.mem_cons_of_mem selection hcandidate)

theorem responseNamesNodup_tail {selection : Selection} {selectionSet : List Selection}
    : responseNamesNodup (selection :: selectionSet)
      -> responseNamesNodup selectionSet := by
  intro hnodup
  cases selection with
  | field responseName fieldName arguments directives childSelectionSet =>
      simpa [responseNamesNodup] using
        (List.nodup_cons.mp
          (by
            simpa [responseNamesNodup, Selection.responseName?] using
              hnodup)).2
  | inlineFragment typeCondition directives childSelectionSet =>
      change responseNamesNodup selectionSet
      exact hnodup

theorem inlineFragmentTypeConditionsNodup_tail
    {selection : Selection} {selectionSet : List Selection}
    : inlineFragmentTypeConditionsNodup (selection :: selectionSet)
      -> inlineFragmentTypeConditionsNodup selectionSet := by
  intro hnodup
  cases selection with
  | field responseName fieldName arguments directives childSelectionSet =>
      change inlineFragmentTypeConditionsNodup selectionSet
      exact hnodup
  | inlineFragment typeCondition directives childSelectionSet =>
      cases typeCondition with
      | none =>
          change inlineFragmentTypeConditionsNodup selectionSet
          exact hnodup
      | some typeCondition =>
          simpa [inlineFragmentTypeConditionsNodup, inlineFragmentTypeCondition?]
            using
            (List.nodup_cons.mp
              (by
                simpa [inlineFragmentTypeConditionsNodup,
                  inlineFragmentTypeCondition?] using hnodup)).2

theorem selectionSetNonRedundant_tail
    {selection : Selection} {selectionSet : List Selection}
    : selectionSetNonRedundant (selection :: selectionSet)
      -> selectionSetNonRedundant selectionSet := by
  intro hnonRedundant
  unfold selectionSetNonRedundant at hnonRedundant ⊢
  exact ⟨
    responseNamesNodup_tail hnonRedundant.1,
    inlineFragmentTypeConditionsNodup_tail hnonRedundant.2.1,
    by
      intro candidate hcandidate
      exact hnonRedundant.2.2 candidate
        (List.mem_cons_of_mem selection hcandidate)
  ⟩

theorem selectionSetNormal_tail
    {schema : Schema} {parentType : Name}
    {selection : Selection} {selectionSet : List Selection}
    : selectionSetNormal schema parentType (selection :: selectionSet)
      -> selectionSetNormal schema parentType selectionSet := by
  intro hnormal
  exact ⟨selectionSetGroundTyped_tail hnormal.1, selectionSetNonRedundant_tail hnormal.2⟩

theorem selectionSet_field_mem_of_allFields_responseName_mem
    {selectionSet : List Selection} {responseName : Name}
    : selectionsAllFields selectionSet
      -> responseName ∈ selectionSet.filterMap Selection.responseName?
      -> ∃ fieldName arguments directives childSelectionSet,
          Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet := by
  intro hallFields hmem
  induction selectionSet with
  | nil =>
      simp at hmem
  | cons selection rest ih =>
      have hheadField : Selection.isField selection :=
        hallFields selection (by simp)
      have hrestAllFields :
          selectionsAllFields rest :=
        selectionsAllFields_tail hallFields
      cases selection with
      | field fieldResponseName fieldName arguments directives childSelectionSet =>
          have hmemCons :
              responseName ∈
                fieldResponseName :: rest.filterMap Selection.responseName? := by
            simpa [Selection.responseName?] using hmem
          rcases List.mem_cons.mp hmemCons with hhead | htail
          · subst responseName
            exact ⟨fieldName, arguments, directives, childSelectionSet,
              by simp⟩
          · rcases ih hrestAllFields htail with
              ⟨matchedFieldName, matchedArguments, matchedDirectives,
                matchedChildSelectionSet, hmatchedMem⟩
            exact ⟨matchedFieldName, matchedArguments, matchedDirectives,
              matchedChildSelectionSet,
              List.mem_cons_of_mem
                (Selection.field fieldResponseName fieldName arguments
                  directives childSelectionSet)
                hmatchedMem⟩
      | inlineFragment typeCondition directives childSelectionSet =>
          simp [Selection.isField] at hheadField

theorem selectionSet_field_mem_of_allFields_nonempty {selectionSet : List Selection}
    : selectionsAllFields selectionSet
      -> selectionSet ≠ []
      -> ∃ responseName fieldName arguments directives childSelectionSet,
          Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet := by
  intro hallFields hnonempty
  cases selectionSet with
  | nil =>
      exact False.elim (hnonempty rfl)
  | cons selection rest =>
      have hheadField : Selection.isField selection :=
        hallFields selection (by simp)
      cases selection with
      | field responseName fieldName arguments directives childSelectionSet =>
          exact ⟨responseName, fieldName, arguments, directives,
            childSelectionSet, by simp⟩
      | inlineFragment typeCondition directives childSelectionSet =>
          simp [Selection.isField] at hheadField

theorem selectionSetNormal_field_mem_of_object_nonempty
    {schema : Schema} {parentType : Name} {selectionSet : List Selection}
    : selectionSetNormal schema parentType selectionSet
      -> objectTypeNameBool schema parentType = true
      -> selectionSet ≠ []
      -> ∃ responseName fieldName arguments directives childSelectionSet,
          Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet := by
  intro hnormal hobject hnonempty
  exact selectionSet_field_mem_of_allFields_nonempty
    (selectionSetNormal_allFields_of_object hnormal hobject) hnonempty

theorem selectionSet_inlineFragment_mem_of_allInlineFragments_typeCondition_mem
    {selectionSet : List Selection} {typeCondition : Name}
    : selectionsAllInlineFragments selectionSet
      -> typeCondition ∈ selectionSet.filterMap inlineFragmentTypeCondition?
      -> ∃ directives childSelectionSet,
          Selection.inlineFragment (some typeCondition) directives childSelectionSet
          ∈ selectionSet := by
  intro hallInline hmem
  induction selectionSet with
  | nil =>
      simp at hmem
  | cons selection rest ih =>
      have hheadInline : Selection.isInlineFragment selection :=
        hallInline selection (by simp)
      have hrestAllInline :
          selectionsAllInlineFragments rest :=
        selectionsAllInlineFragments_tail hallInline
      cases selection with
      | field responseName fieldName arguments directives childSelectionSet =>
          simp [Selection.isInlineFragment] at hheadInline
      | inlineFragment maybeTypeCondition directives childSelectionSet =>
          cases maybeTypeCondition with
          | none =>
              rcases ih hrestAllInline (by
                  simpa [inlineFragmentTypeCondition?] using hmem) with
                ⟨matchedDirectives, matchedChildSelectionSet, hmatchedMem⟩
              exact ⟨matchedDirectives, matchedChildSelectionSet,
                List.mem_cons_of_mem
                  (Selection.inlineFragment none directives childSelectionSet)
                  hmatchedMem⟩
          | some headTypeCondition =>
              have hmemCons :
                  typeCondition ∈
                    headTypeCondition ::
                      rest.filterMap inlineFragmentTypeCondition? := by
                simpa [inlineFragmentTypeCondition?] using hmem
              rcases List.mem_cons.mp hmemCons with hhead | htail
              · subst typeCondition
                exact ⟨directives, childSelectionSet, by simp⟩
              · rcases ih hrestAllInline htail with
                  ⟨matchedDirectives, matchedChildSelectionSet, hmatchedMem⟩
                exact ⟨matchedDirectives, matchedChildSelectionSet,
                  List.mem_cons_of_mem
                    (Selection.inlineFragment (some headTypeCondition)
                      directives childSelectionSet)
                    hmatchedMem⟩

theorem selectionSetNormal_field_mem_of_object_responseName_mem
    {schema : Schema} {parentType : Name} {selectionSet : List Selection}
    {responseName : Name}
    : selectionSetNormal schema parentType selectionSet
      -> objectTypeNameBool schema parentType = true
      -> responseName ∈ selectionSet.filterMap Selection.responseName?
      -> ∃ fieldName arguments directives childSelectionSet,
          Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet := by
  intro hnormal hobject hmem
  exact selectionSet_field_mem_of_allFields_responseName_mem
    (selectionSetNormal_allFields_of_object hnormal hobject) hmem

theorem selectionSetNormal_inlineFragment_mem_of_abstract_typeCondition_mem
    {schema : Schema} {parentType : Name} {selectionSet : List Selection}
    {typeCondition : Name}
    : selectionSetNormal schema parentType selectionSet
      -> objectTypeNameBool schema parentType = false
      -> typeCondition ∈ selectionSet.filterMap inlineFragmentTypeCondition?
      -> ∃ directives childSelectionSet,
          Selection.inlineFragment (some typeCondition) directives childSelectionSet
          ∈ selectionSet := by
  intro hnormal hobject hmem
  exact selectionSet_inlineFragment_mem_of_allInlineFragments_typeCondition_mem
    (selectionSetNormal_allInlineFragments_of_abstract hnormal hobject) hmem

theorem selectionDirectiveFree_of_mem
    {selectionSet : List Selection} {selection : Selection}
    : selectionSetDirectiveFree selectionSet
      -> selection ∈ selectionSet
      -> selectionDirectiveFree selection := by
  intro hfree
  induction selectionSet with
  | nil =>
      intro hmem
      simp at hmem
  | cons head rest ih =>
      intro hmem
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst head
        exact selectionSetDirectiveFree_head hfree
      · exact ih (selectionSetDirectiveFree_tail hfree) htail

theorem selectionSetDirectiveFree_field_directives_nil_of_mem
    {selectionSet : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet : List Selection}
    : selectionSetDirectiveFree selectionSet
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> directives = [] := by
  intro hfree hmem
  have hselectionFree :
      selectionDirectiveFree
        (Selection.field responseName fieldName arguments directives
          childSelectionSet) :=
    selectionDirectiveFree_of_mem hfree hmem
  simpa [selectionDirectiveFree] using hselectionFree.1

theorem selectionSetDirectiveFree_inlineFragment_directives_nil_of_mem
    {selectionSet : List Selection}
    {typeCondition : Option Name} {directives : List DirectiveApplication}
    {childSelectionSet : List Selection}
    : selectionSetDirectiveFree selectionSet
      -> Selection.inlineFragment typeCondition directives childSelectionSet
          ∈ selectionSet
      -> directives = [] := by
  intro hfree hmem
  have hselectionFree :
      selectionDirectiveFree
        (Selection.inlineFragment typeCondition directives childSelectionSet) :=
    selectionDirectiveFree_of_mem hfree hmem
  simpa [selectionDirectiveFree] using hselectionFree.1

theorem selectionSetDirectiveFree_field_child_of_mem
    {selectionSet : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet : List Selection}
    : selectionSetDirectiveFree selectionSet
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> selectionSetDirectiveFree childSelectionSet := by
  intro hfree hmem
  have hselectionFree :
      selectionDirectiveFree
        (Selection.field responseName fieldName arguments directives
          childSelectionSet) :=
    selectionDirectiveFree_of_mem hfree hmem
  simpa [selectionDirectiveFree] using hselectionFree.2

theorem selectionSetDirectiveFree_inlineFragment_child_of_mem
    {selectionSet : List Selection}
    {typeCondition : Option Name} {directives : List DirectiveApplication}
    {childSelectionSet : List Selection}
    : selectionSetDirectiveFree selectionSet
      -> Selection.inlineFragment typeCondition directives childSelectionSet
          ∈ selectionSet
      -> selectionSetDirectiveFree childSelectionSet := by
  intro hfree hmem
  have hselectionFree :
      selectionDirectiveFree
        (Selection.inlineFragment typeCondition directives childSelectionSet) :=
    selectionDirectiveFree_of_mem hfree hmem
  simpa [selectionDirectiveFree] using hselectionFree.2

theorem selectionSetNormal_field_child_of_mem_with_returnType
    {schema : Schema} {parentType responseName fieldName : Name}
    {arguments : List Argument} {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    : selectionSetNormal schema parentType selectionSet
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> ∃ returnType,
          schema.fieldReturnType? parentType fieldName = some returnType
          ∧ selectionSetNormal schema returnType childSelectionSet := by
  intro hnormal hmem
  rcases hnormal with ⟨hground, hnonRedundant⟩
  unfold selectionSetGroundTyped at hground
  have hselectionGround :
      selectionGroundTyped schema parentType
        (Selection.field responseName fieldName arguments directives
          childSelectionSet) :=
    hground.2 _ hmem
  unfold selectionGroundTyped at hselectionGround
  rcases hselectionGround with ⟨returnType, hreturn, hchildGround⟩
  unfold selectionSetNonRedundant at hnonRedundant
  have hchildNonRedundant :
      selectionSetNonRedundant childSelectionSet := by
    have hselectionNonRedundant :
        selectionNonRedundant
          (Selection.field responseName fieldName arguments directives
            childSelectionSet) :=
      hnonRedundant.2.2 _ hmem
    simpa [selectionNonRedundant] using hselectionNonRedundant
  exact ⟨
    returnType,
    hreturn,
    (⟨hchildGround, hchildNonRedundant⟩
      : selectionSetNormal schema returnType childSelectionSet)
  ⟩

theorem selectionSetNormal_inlineFragment_child_of_mem
    {schema : Schema} {parentType typeCondition : Name}
    {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    : selectionSetNormal schema parentType selectionSet
      -> Selection.inlineFragment (some typeCondition) directives childSelectionSet
          ∈ selectionSet
      -> schema.objectType typeCondition
          ∧ selectionSetNormal schema typeCondition childSelectionSet := by
  intro hnormal hmem
  rcases hnormal with ⟨hground, hnonRedundant⟩
  unfold selectionSetGroundTyped at hground
  have hselectionGround :
      selectionGroundTyped schema parentType
        (Selection.inlineFragment (some typeCondition) directives
          childSelectionSet) :=
    hground.2 _ hmem
  unfold selectionGroundTyped at hselectionGround
  rcases hselectionGround with
    ⟨htypeConditionObject, hchildGround⟩
  unfold selectionSetNonRedundant at hnonRedundant
  have hchildNonRedundant :
      selectionSetNonRedundant childSelectionSet := by
    have hselectionNonRedundant :
        selectionNonRedundant
          (Selection.inlineFragment (some typeCondition) directives
            childSelectionSet) :=
      hnonRedundant.2.2 _ hmem
    simpa [selectionNonRedundant] using hselectionNonRedundant
  exact ⟨
    htypeConditionObject,
    (⟨hchildGround, hchildNonRedundant⟩
      : selectionSetNormal schema typeCondition childSelectionSet)
  ⟩

theorem mem_erase_of_ne_of_mem {α : Type} [BEq α] [LawfulBEq α] {a b : α} {items : List α}
    : a ≠ b -> a ∈ items -> a ∈ items.erase b := by
  intro hne hmem
  induction items with
  | nil =>
      simp at hmem
  | cons head tail ih =>
      by_cases hhead : head = b
      · subst head
        rw [List.erase_cons_head]
        rcases List.mem_cons.mp hmem with hsame | htail
        · exact False.elim (hne hsame)
        · exact htail
      · have htailErase : ¬(head == b) = true := by
          have hbeq : (head == b) = false :=
            (beq_eq_false_iff_ne).2 hhead
          simp [hbeq]
        rw [List.erase_cons_tail htailErase]
        rcases List.mem_cons.mp hmem with hsame | htail
        · exact List.mem_cons.mpr (Or.inl hsame)
        · exact List.mem_cons_of_mem head (ih htail)

theorem not_mem_erase_self {α : Type} [BEq α] [LawfulBEq α] (a : α)
    : ∀ items : List α, items.Nodup -> a ∉ items.erase a
  | [], _hnodup => by
      simp
  | head :: tail, hnodup => by
      have hparts : head ∉ tail ∧ tail.Nodup := by
        simpa using hnodup
      have hheadNotMem : head ∉ tail := hparts.1
      have htailNodup : tail.Nodup := hparts.2
      by_cases hhead : head = a
      · subst head
        rw [List.erase_cons_head]
        intro hmem
        exact hheadNotMem hmem
      · have htailErase : ¬(head == a) = true := by
          have hbeq : (head == a) = false :=
            (beq_eq_false_iff_ne).2 hhead
          simp [hbeq]
        rw [List.erase_cons_tail htailErase]
        intro hmem
        rcases List.mem_cons.mp hmem with hheadMem | htailMem
        · exact hhead hheadMem.symm
        · exact not_mem_erase_self a tail htailNodup htailMem

theorem listPermOfNodupSubsetSubset {α : Type} [BEq α] [LawfulBEq α] {left right : List α}
    : left.Nodup
      -> right.Nodup
      -> (∀ item, item ∈ left -> item ∈ right)
      -> (∀ item, item ∈ right -> item ∈ left)
      -> left.Perm right := by
  intro hleftNodup
  induction left generalizing right with
  | nil =>
      intro _hrightNodup _hleftSubset hrightSubset
      cases right with
      | nil =>
          exact List.Perm.nil
      | cons head tail =>
          have hhead : head ∈ ([] : List α) :=
            hrightSubset head (by simp)
          simp at hhead
  | cons head tail ih =>
      intro hrightNodup hleftSubset hrightSubset
      have hleftParts : head ∉ tail ∧ tail.Nodup := by
        simpa using hleftNodup
      have hheadNotMem : head ∉ tail := hleftParts.1
      have htailNodup : tail.Nodup := hleftParts.2
      have hheadRight : head ∈ right :=
        hleftSubset head (by simp)
      have hrightEraseNodup : (right.erase head).Nodup :=
        List.Nodup.erase head hrightNodup
      have htailSubset :
          ∀ item, item ∈ tail -> item ∈ right.erase head := by
        intro item hitem
        have hitemRight : item ∈ right :=
          hleftSubset item (List.mem_cons_of_mem head hitem)
        have hne : item ≠ head := by
          intro hitemEq
          subst item
          exact hheadNotMem hitem
        exact mem_erase_of_ne_of_mem hne hitemRight
      have hrightEraseSubset :
          ∀ item, item ∈ right.erase head -> item ∈ tail := by
        intro item hitemErase
        have hitemRight : item ∈ right :=
          List.mem_of_mem_erase hitemErase
        have hitemLeft : item ∈ head :: tail :=
          hrightSubset item hitemRight
        rcases List.mem_cons.mp hitemLeft with hitemHead | hitemTail
        · subst item
          exact False.elim
            ((not_mem_erase_self head right hrightNodup) hitemErase)
        · exact hitemTail
      have htailPerm : tail.Perm (right.erase head) :=
        ih htailNodup hrightEraseNodup htailSubset hrightEraseSubset
      exact (List.Perm.cons head htailPerm).trans (List.perm_cons_erase hheadRight).symm

theorem responseNamesNodup_remove_middle_field
    {pref suffix : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet : List Selection}
    : responseNamesNodup
        (pref
          ++ Selection.field responseName fieldName arguments directives childSelectionSet
              :: suffix)
      -> responseNamesNodup (pref ++ suffix) := by
  intro hnodup
  unfold responseNamesNodup at hnodup ⊢
  have hnames :
      (pref.filterMap Selection.responseName? ++
        responseName :: suffix.filterMap Selection.responseName?).Nodup := by
    simpa [Selection.responseName?, List.filterMap_append] using hnodup
  have hparts := List.nodup_append.mp hnames
  have hremoved :
      (pref.filterMap Selection.responseName? ++
        suffix.filterMap Selection.responseName?).Nodup :=
    List.nodup_append.mpr
      ⟨hparts.1, (List.nodup_cons.mp hparts.2.1).2, by
        intro leftName hleft rightName hright heq
        exact hparts.2.2 leftName hleft rightName (by simp [hright]) heq⟩
  simpa [List.filterMap_append] using hremoved

theorem responseName_not_mem_remove_middle_field
    {pref suffix : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet : List Selection}
    : responseNamesNodup
        (pref
          ++ Selection.field responseName fieldName arguments directives childSelectionSet
              :: suffix)
      -> responseName ∉ (pref ++ suffix).filterMap Selection.responseName? := by
  intro hnodup hmem
  unfold responseNamesNodup at hnodup
  have hnames :
      (pref.filterMap Selection.responseName? ++
        responseName :: suffix.filterMap Selection.responseName?).Nodup := by
    simpa [Selection.responseName?, List.filterMap_append] using hnodup
  have hmemSplit :
      responseName ∈ pref.filterMap Selection.responseName?
        ∨ responseName ∈ suffix.filterMap Selection.responseName? := by
    simpa [List.filterMap_append] using hmem
  have hparts := List.nodup_append.mp hnames
  rcases hmemSplit with hprefix | hsuffix
  · exact hparts.2.2 responseName hprefix responseName (by simp) rfl
  · have hnotSuffix :
        responseName ∉ suffix.filterMap Selection.responseName? :=
      (List.nodup_cons.mp hparts.2.1).1
    exact hnotSuffix hsuffix

theorem field_eq_of_responseNamesNodup_mem
    {selectionSet : List Selection}
    {responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    : responseNamesNodup selectionSet
      -> Selection.field responseName leftFieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ selectionSet
      -> Selection.field responseName rightFieldName rightArguments
            rightDirectives rightChildSelectionSet
          ∈ selectionSet
      -> Selection.field responseName leftFieldName leftArguments leftDirectives
            leftChildSelectionSet
          = Selection.field responseName rightFieldName rightArguments
              rightDirectives rightChildSelectionSet := by
  intro hnodup hleftMem hrightMem
  rcases List.mem_iff_append.mp hleftMem with
    ⟨pref, suffix, hselectionSet⟩
  subst selectionSet
  have hrightCases :
      Selection.field responseName rightFieldName rightArguments
          rightDirectives rightChildSelectionSet ∈
        pref ++ suffix
        ∨
      Selection.field responseName rightFieldName rightArguments
          rightDirectives rightChildSelectionSet =
        Selection.field responseName leftFieldName leftArguments
          leftDirectives leftChildSelectionSet := by
    have hmem :
        Selection.field responseName rightFieldName rightArguments
            rightDirectives rightChildSelectionSet ∈
          pref ++
            Selection.field responseName leftFieldName leftArguments
              leftDirectives leftChildSelectionSet :: suffix := hrightMem
    rw [List.mem_append] at hmem
    rcases hmem with hpref | htail
    · exact Or.inl (List.mem_append_left suffix hpref)
    · rw [List.mem_cons] at htail
      rcases htail with hhead | hsuffix
      · exact Or.inr hhead
      · exact Or.inl (List.mem_append_right pref hsuffix)
  rcases hrightCases with hrightRest | hrightEq
  · have hnotMem :
        responseName ∉ (pref ++ suffix).filterMap Selection.responseName? :=
      responseName_not_mem_remove_middle_field hnodup
    have hresponseMem :
        responseName ∈ (pref ++ suffix).filterMap Selection.responseName? :=
      List.mem_filterMap.mpr
        ⟨Selection.field responseName rightFieldName rightArguments
          rightDirectives rightChildSelectionSet, hrightRest, by
          simp [Selection.responseName?]⟩
    exact False.elim (hnotMem hresponseMem)
  · exact hrightEq.symm

theorem field_components_eq_of_responseNamesNodup_mem
    {selectionSet : List Selection}
    {responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    : responseNamesNodup selectionSet
      -> Selection.field responseName leftFieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ selectionSet
      -> Selection.field responseName rightFieldName rightArguments
            rightDirectives rightChildSelectionSet
          ∈ selectionSet
      -> leftFieldName = rightFieldName
          ∧ leftArguments = rightArguments
          ∧ leftDirectives = rightDirectives
          ∧ leftChildSelectionSet = rightChildSelectionSet := by
  intro hnodup hleftMem hrightMem
  have hfieldEq :=
    field_eq_of_responseNamesNodup_mem hnodup hleftMem hrightMem
  cases hfieldEq
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem field_components_eq_of_selectionSetNormal_responseName_mem
    {schema : Schema} {parentType : Name}
    {selectionSet : List Selection}
    {responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    : selectionSetNormal schema parentType selectionSet
      -> Selection.field responseName leftFieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ selectionSet
      -> Selection.field responseName rightFieldName rightArguments
            rightDirectives rightChildSelectionSet
          ∈ selectionSet
      -> leftFieldName = rightFieldName
          ∧ leftArguments = rightArguments
          ∧ leftDirectives = rightDirectives
          ∧ leftChildSelectionSet = rightChildSelectionSet := by
  intro hnormal
  exact
    field_components_eq_of_responseNamesNodup_mem
      (selectionSetNormal_responseNamesNodup hnormal)

theorem inlineFragmentTypeConditionsNodup_remove_middle_inlineFragment
    {pref suffix : List Selection}
    {typeCondition : Name} {directives : List DirectiveApplication}
    {childSelectionSet : List Selection}
    : inlineFragmentTypeConditionsNodup
        (pref
          ++ Selection.inlineFragment (some typeCondition) directives childSelectionSet
              :: suffix)
      -> inlineFragmentTypeConditionsNodup (pref ++ suffix) := by
  intro hnodup
  unfold inlineFragmentTypeConditionsNodup at hnodup ⊢
  have hconditions :
      (pref.filterMap inlineFragmentTypeCondition?
        ++ typeCondition :: suffix.filterMap inlineFragmentTypeCondition?).Nodup := by
    simpa [inlineFragmentTypeCondition?, List.filterMap_append] using hnodup
  have hparts := List.nodup_append.mp hconditions
  have hremoved :
      (pref.filterMap inlineFragmentTypeCondition?
        ++ suffix.filterMap inlineFragmentTypeCondition?).Nodup :=
    List.nodup_append.mpr
      ⟨hparts.1, (List.nodup_cons.mp hparts.2.1).2, by
        intro leftTypeCondition hleft rightTypeCondition hright heq
        exact hparts.2.2 leftTypeCondition hleft rightTypeCondition
          (by simp [hright]) heq⟩
  simpa [inlineFragmentTypeCondition?, List.filterMap_append] using hremoved

theorem inlineFragmentTypeCondition_not_mem_remove_middle_inlineFragment
    {pref suffix : List Selection}
    {typeCondition : Name} {directives : List DirectiveApplication}
    {childSelectionSet : List Selection}
    : inlineFragmentTypeConditionsNodup
        (pref
          ++ Selection.inlineFragment (some typeCondition) directives childSelectionSet
              :: suffix)
      -> typeCondition ∉ (pref ++ suffix).filterMap inlineFragmentTypeCondition? := by
  intro hnodup hmem
  unfold inlineFragmentTypeConditionsNodup at hnodup
  have hconditions :
      (pref.filterMap inlineFragmentTypeCondition?
        ++ typeCondition :: suffix.filterMap inlineFragmentTypeCondition?).Nodup := by
    simpa [inlineFragmentTypeCondition?, List.filterMap_append] using hnodup
  have hmemSplit :
      typeCondition ∈ pref.filterMap inlineFragmentTypeCondition?
        ∨ typeCondition ∈ suffix.filterMap inlineFragmentTypeCondition? := by
    simpa [List.filterMap_append] using hmem
  have hparts := List.nodup_append.mp hconditions
  rcases hmemSplit with hprefix | hsuffix
  · exact hparts.2.2 typeCondition hprefix typeCondition (by simp) rfl
  · have hnotSuffix :
        typeCondition ∉ suffix.filterMap inlineFragmentTypeCondition? :=
      (List.nodup_cons.mp hparts.2.1).1
    exact hnotSuffix hsuffix

theorem selectionSet_size_append_eq (left right : List Selection)
    : SelectionSet.size (left ++ right)
      = SelectionSet.size left + SelectionSet.size right := by
  induction left with
  | nil =>
      simp [SelectionSet.size]
  | cons selection rest ih =>
      simp [SelectionSet.size, ih, Nat.add_assoc]

theorem selectionSet_size_field_child_lt_of_mem
    {responseName fieldName : Name}
    {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    : Selection.field responseName fieldName arguments directives childSelectionSet
        ∈ selectionSet
      -> SelectionSet.size childSelectionSet < SelectionSet.size selectionSet := by
  intro hmem
  rcases List.mem_iff_append.mp hmem with ⟨pref, suffix, hselectionSet⟩
  subst selectionSet
  rw [selectionSet_size_append_eq]
  simp [SelectionSet.size, Selection.size]
  omega

theorem selectionSet_size_inlineFragment_child_lt_of_mem
    {typeCondition : Option Name}
    {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    : Selection.inlineFragment typeCondition directives childSelectionSet ∈ selectionSet
      -> SelectionSet.size childSelectionSet < SelectionSet.size selectionSet := by
  intro hmem
  rcases List.mem_iff_append.mp hmem with ⟨pref, suffix, hselectionSet⟩
  subst selectionSet
  rw [selectionSet_size_append_eq]
  simp [SelectionSet.size, Selection.size]
  omega

mutual
  theorem selectionEqualUpToReordering_refl
      : ∀ selection, SelectionEqualUpToReordering selection selection
    | .field responseName fieldName arguments directives selectionSet =>
        SelectionEqualUpToReordering.field responseName fieldName directives
          (argumentsEquivalent_refl_forSyntaxDiff arguments)
          (selectionSetEqualUpToReordering_refl selectionSet)
    | .inlineFragment typeCondition directives selectionSet =>
        SelectionEqualUpToReordering.inlineFragment typeCondition directives
          (selectionSetEqualUpToReordering_refl selectionSet)

  theorem selectionSetEqualUpToReordering_refl
      : ∀ selectionSet, SelectionSetEqualUpToReordering selectionSet selectionSet
    | [] => by
        exact SelectionSetEqualUpToReordering.paired [] List.Perm.nil
          List.Perm.nil
          (by intro pair hpair; simp at hpair)
    | selection :: rest => by
        rcases selectionSetEqualUpToReordering_refl rest with
          ⟨pairs, hleft, hright, hrelations⟩
        apply SelectionSetEqualUpToReordering.paired
          ((selection, selection) :: pairs)
        · exact hleft.cons selection
        · exact hright.cons selection
        · intro pair hpair
          rcases List.mem_cons.mp hpair with hhead | htail
          · subst pair
            exact selectionEqualUpToReordering_refl selection
          · exact hrelations pair htail
end

theorem selectionSetEqualUpToReordering_of_field_responseName_matches
    : ∀ left right,
        selectionsAllFields left
        -> selectionsAllFields right
        -> responseNamesNodup left
        -> responseNamesNodup right
        -> (∀ responseName fieldName arguments directives childSelectionSet,
              Selection.field responseName fieldName arguments directives
                  childSelectionSet
                ∈ left
              -> ∃ rightFieldName rightArguments rightDirectives rightChildSelectionSet,
                  Selection.field responseName rightFieldName rightArguments
                      rightDirectives rightChildSelectionSet
                    ∈ right
                  ∧ SelectionEqualUpToReordering
                      (Selection.field responseName fieldName arguments directives
                        childSelectionSet)
                      (Selection.field responseName rightFieldName rightArguments
                        rightDirectives rightChildSelectionSet))
        -> (∀ responseName,
              responseName ∈ right.filterMap Selection.responseName?
              -> responseName ∈ left.filterMap Selection.responseName?)
        -> SelectionSetEqualUpToReordering left right := by
  intro left
  induction left with
  | nil =>
      intro right _hleftAll hrightAll _hleftNodup _hrightNodup _hmatch
        hcoverage
      cases right with
      | nil =>
          exact SelectionSetEqualUpToReordering.paired [] List.Perm.nil
            List.Perm.nil
            (by intro pair hpair; simp at hpair)
      | cons selection rest =>
          have hselectionField : Selection.isField selection :=
            hrightAll selection (by simp)
          cases selection with
          | field responseName fieldName arguments directives childSelectionSet =>
              have hrightName :
                  responseName ∈
                    (Selection.field responseName fieldName arguments directives
                      childSelectionSet :: rest).filterMap
                      Selection.responseName? := by
                simp [Selection.responseName?]
              have hleftName := hcoverage responseName hrightName
              simp at hleftName
          | inlineFragment typeCondition directives childSelectionSet =>
              simp [Selection.isField] at hselectionField
  | cons selection leftRest ih =>
      intro right hleftAll hrightAll hleftNodup hrightNodup hmatch
        hcoverage
      have hselectionField : Selection.isField selection :=
        hleftAll selection (by simp)
      cases selection with
      | inlineFragment typeCondition directives childSelectionSet =>
          simp [Selection.isField] at hselectionField
      | field responseName fieldName arguments directives childSelectionSet =>
          have hleftRestAll :
              selectionsAllFields leftRest :=
            selectionsAllFields_tail hleftAll
          have hleftNodupCons :
              (responseName ::
                leftRest.filterMap Selection.responseName?).Nodup := by
            simpa [responseNamesNodup, Selection.responseName?] using
              hleftNodup
          have hleftHeadNotRest :
              responseName ∉ leftRest.filterMap Selection.responseName? :=
            (List.nodup_cons.mp hleftNodupCons).1
          have hleftRestNodup :
              responseNamesNodup leftRest := by
            simpa [responseNamesNodup] using
              (List.nodup_cons.mp hleftNodupCons).2
          rcases hmatch responseName fieldName arguments directives
              childSelectionSet (by simp) with
            ⟨rightFieldName, rightArguments, rightDirectives,
              rightChildSelectionSet, hrightMem, hselectionEq⟩
          let matchedRight : Selection :=
            Selection.field responseName rightFieldName rightArguments
              rightDirectives rightChildSelectionSet
          rcases (List.mem_iff_append.mp hrightMem) with
            ⟨pref, suffix, hrightEq⟩
          have hrightNodupSplit :
              responseNamesNodup
                (pref ++ matchedRight :: suffix) := by
            simpa [matchedRight, hrightEq] using hrightNodup
          have hrightRestAll :
              selectionsAllFields (pref ++ suffix) := by
            intro candidate hcandidate
            apply hrightAll candidate
            rw [hrightEq]
            rcases List.mem_append.mp hcandidate with hpref | hsuffix
            · exact List.mem_append_left _ hpref
            · exact List.mem_append_right _ (List.mem_cons_of_mem _ hsuffix)
          have hrightRestNodup :
              responseNamesNodup (pref ++ suffix) :=
            responseNamesNodup_remove_middle_field hrightNodupSplit
          have hrightMatchedNotRest :
              responseName ∉
                (pref ++ suffix).filterMap Selection.responseName? :=
            responseName_not_mem_remove_middle_field hrightNodupSplit
          have htailMatch :
              ∀ tailResponseName tailFieldName tailArguments tailDirectives
                tailChildSelectionSet,
                Selection.field tailResponseName tailFieldName tailArguments
                  tailDirectives tailChildSelectionSet ∈ leftRest ->
                  ∃ rightFieldName rightArguments rightDirectives
                    rightChildSelectionSet,
                    Selection.field tailResponseName rightFieldName
                      rightArguments rightDirectives rightChildSelectionSet ∈
                      pref ++ suffix
                      ∧ SelectionEqualUpToReordering
                        (Selection.field tailResponseName tailFieldName
                          tailArguments tailDirectives tailChildSelectionSet)
                        (Selection.field tailResponseName rightFieldName
                          rightArguments rightDirectives
                          rightChildSelectionSet) := by
            intro tailResponseName tailFieldName tailArguments tailDirectives
              tailChildSelectionSet htailMem
            rcases hmatch tailResponseName tailFieldName tailArguments
                tailDirectives tailChildSelectionSet
                (List.mem_cons_of_mem _ htailMem) with
              ⟨matchedFieldName, matchedArguments, matchedDirectives,
                matchedChildSelectionSet, hmatchedMem, hmatchedEq⟩
            have hmatchedMemSplit :
                Selection.field tailResponseName matchedFieldName
                  matchedArguments matchedDirectives matchedChildSelectionSet ∈
                    pref ++ matchedRight :: suffix := by
              simpa [matchedRight, hrightEq] using hmatchedMem
            have hmatchedMemRest :
                Selection.field tailResponseName matchedFieldName
                  matchedArguments matchedDirectives matchedChildSelectionSet ∈
                    pref ++ suffix := by
              rcases List.mem_append.mp hmatchedMemSplit with hpref | htail
              · exact List.mem_append_left _ hpref
              · rcases List.mem_cons.mp htail with hhead | hsuffix
                · have hresponseEq : tailResponseName = responseName := by
                    have hsome :
                        some tailResponseName = some responseName := by
                      simpa [matchedRight, Selection.responseName?] using
                        congrArg Selection.responseName? hhead
                    simpa using hsome
                  have htailResponseMem :
                      tailResponseName ∈
                        leftRest.filterMap Selection.responseName? :=
                    List.mem_filterMap.mpr
                      ⟨Selection.field tailResponseName tailFieldName
                        tailArguments tailDirectives tailChildSelectionSet,
                        htailMem, by simp [Selection.responseName?]⟩
                  exact False.elim
                    (hleftHeadNotRest
                      (by simpa [hresponseEq] using htailResponseMem))
                · exact List.mem_append_right _ hsuffix
            exact ⟨matchedFieldName, matchedArguments, matchedDirectives,
              matchedChildSelectionSet, hmatchedMemRest, hmatchedEq⟩
          have htailCoverage :
              ∀ tailResponseName,
                tailResponseName ∈
                  (pref ++ suffix).filterMap Selection.responseName? ->
                  tailResponseName ∈
                    leftRest.filterMap Selection.responseName? := by
            intro tailResponseName htailRightName
            rcases List.mem_filterMap.mp htailRightName with
              ⟨rightSelection, hrightSelectionRest, hrightSelectionName⟩
            have hrightSelectionOriginal :
                rightSelection ∈ right := by
              rw [hrightEq]
              rcases List.mem_append.mp hrightSelectionRest with hpref | hsuffix
              · exact List.mem_append_left _ hpref
              · exact List.mem_append_right _
                  (List.mem_cons_of_mem _ hsuffix)
            have hrightNameOriginal :
                tailResponseName ∈ right.filterMap Selection.responseName? :=
              List.mem_filterMap.mpr
                ⟨rightSelection, hrightSelectionOriginal,
                  hrightSelectionName⟩
            have hleftName :
                tailResponseName ∈
                  (Selection.field responseName fieldName arguments directives
                    childSelectionSet :: leftRest).filterMap
                    Selection.responseName? :=
              hcoverage tailResponseName hrightNameOriginal
            have hleftSplit :
                tailResponseName = responseName
                  ∨ tailResponseName ∈
                    leftRest.filterMap Selection.responseName? := by
              simpa [Selection.responseName?] using hleftName
            rcases hleftSplit with hhead | htail
            · exact False.elim
                (hrightMatchedNotRest
                  (by simpa [hhead] using htailRightName))
            · exact htail
          rcases ih (pref ++ suffix) hleftRestAll hrightRestAll
              hleftRestNodup hrightRestNodup htailMatch htailCoverage with
            ⟨pairs, hleftPerm, hrightPerm, hpairRelations⟩
          apply SelectionSetEqualUpToReordering.paired
            ((Selection.field responseName fieldName arguments directives
                childSelectionSet, matchedRight) :: pairs)
          · exact hleftPerm.cons
              (Selection.field responseName fieldName arguments directives
                childSelectionSet)
          · have hrightReinsert :
                (matchedRight :: pairs.map Prod.snd).Perm
                  (pref ++ matchedRight :: suffix) :=
              (hrightPerm.cons matchedRight).trans List.perm_middle.symm
            simpa [matchedRight, hrightEq] using hrightReinsert
          · intro pair hpair
            rcases List.mem_cons.mp hpair with hhead | htail
            · subst pair
              exact hselectionEq
            · exact hpairRelations pair htail

theorem selectionSetEqualUpToReordering_of_inlineFragment_typeCondition_matches
    : ∀ left right,
        inlineFragmentTypeConditionsNodup left
        -> inlineFragmentTypeConditionsNodup right
        -> (∀ selection,
              selection ∈ left
              -> ∃ typeCondition directives childSelectionSet,
                  selection
                  = Selection.inlineFragment (some typeCondition) directives
                      childSelectionSet)
        -> (∀ selection,
              selection ∈ right
              -> ∃ typeCondition directives childSelectionSet,
                  selection
                  = Selection.inlineFragment (some typeCondition) directives
                      childSelectionSet)
        -> (∀ typeCondition directives childSelectionSet,
              Selection.inlineFragment (some typeCondition) directives childSelectionSet
                ∈ left
              -> ∃ rightDirectives rightChildSelectionSet,
                  Selection.inlineFragment (some typeCondition) rightDirectives
                      rightChildSelectionSet
                    ∈ right
                  ∧ SelectionEqualUpToReordering
                      (Selection.inlineFragment (some typeCondition) directives
                        childSelectionSet)
                      (Selection.inlineFragment (some typeCondition) rightDirectives
                        rightChildSelectionSet))
        -> (∀ typeCondition,
              typeCondition ∈ right.filterMap inlineFragmentTypeCondition?
              -> typeCondition ∈ left.filterMap inlineFragmentTypeCondition?)
        -> SelectionSetEqualUpToReordering left right := by
  intro left
  induction left with
  | nil =>
      intro right _hleftNodup _hrightNodup _hleftSome hrightSome _hmatch
        hcoverage
      cases right with
      | nil =>
          exact SelectionSetEqualUpToReordering.paired [] List.Perm.nil
            List.Perm.nil
            (by intro pair hpair; simp at hpair)
      | cons selection rest =>
          rcases hrightSome selection (by simp) with
            ⟨typeCondition, directives, childSelectionSet, hselection⟩
          subst selection
          have hrightTypeCondition :
              typeCondition ∈
                (Selection.inlineFragment (some typeCondition) directives
                  childSelectionSet :: rest).filterMap
                  inlineFragmentTypeCondition? := by
            simp [inlineFragmentTypeCondition?]
          have hleftTypeCondition :=
            hcoverage typeCondition hrightTypeCondition
          simp at hleftTypeCondition
  | cons selection leftRest ih =>
      intro right hleftNodup hrightNodup hleftSome hrightSome hmatch
        hcoverage
      rcases hleftSome selection (by simp) with
        ⟨typeCondition, directives, childSelectionSet, hselection⟩
      subst selection
      have hleftRestSome :
          ∀ selection, selection ∈ leftRest ->
            ∃ typeCondition directives childSelectionSet,
              selection =
                Selection.inlineFragment (some typeCondition) directives
                  childSelectionSet := by
        intro candidate hcandidate
        exact hleftSome candidate (List.mem_cons_of_mem _ hcandidate)
      have hleftNodupCons :
          (typeCondition ::
            leftRest.filterMap inlineFragmentTypeCondition?).Nodup := by
        simpa [inlineFragmentTypeConditionsNodup, inlineFragmentTypeCondition?]
          using hleftNodup
      have hleftHeadNotRest :
          typeCondition ∉ leftRest.filterMap inlineFragmentTypeCondition? :=
        (List.nodup_cons.mp hleftNodupCons).1
      have hleftRestNodup :
          inlineFragmentTypeConditionsNodup leftRest := by
        simpa [inlineFragmentTypeConditionsNodup, inlineFragmentTypeCondition?]
          using (List.nodup_cons.mp hleftNodupCons).2
      rcases hmatch typeCondition directives childSelectionSet (by simp) with
        ⟨rightDirectives, rightChildSelectionSet, hrightMem,
          hselectionEq⟩
      let matchedRight : Selection :=
        Selection.inlineFragment (some typeCondition) rightDirectives
          rightChildSelectionSet
      rcases (List.mem_iff_append.mp hrightMem) with
        ⟨pref, suffix, hrightEq⟩
      have hrightNodupSplit :
          inlineFragmentTypeConditionsNodup
            (pref ++ matchedRight :: suffix) := by
        simpa [matchedRight, hrightEq] using hrightNodup
      have hrightRestSome :
          ∀ selection, selection ∈ pref ++ suffix ->
            ∃ typeCondition directives childSelectionSet,
              selection =
                Selection.inlineFragment (some typeCondition) directives
                  childSelectionSet := by
        intro candidate hcandidate
        apply hrightSome candidate
        rw [hrightEq]
        rcases List.mem_append.mp hcandidate with hpref | hsuffix
        · exact List.mem_append_left _ hpref
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ hsuffix)
      have hrightRestNodup :
          inlineFragmentTypeConditionsNodup (pref ++ suffix) :=
        inlineFragmentTypeConditionsNodup_remove_middle_inlineFragment
          (by simpa [matchedRight] using hrightNodupSplit)
      have hrightMatchedNotRest :
          typeCondition ∉ (pref ++ suffix).filterMap
            inlineFragmentTypeCondition? :=
        inlineFragmentTypeCondition_not_mem_remove_middle_inlineFragment
          (by simpa [matchedRight] using hrightNodupSplit)
      have htailMatch :
          ∀ tailTypeCondition tailDirectives tailChildSelectionSet,
            Selection.inlineFragment (some tailTypeCondition) tailDirectives
              tailChildSelectionSet ∈ leftRest ->
            ∃ rightDirectives rightChildSelectionSet,
              Selection.inlineFragment (some tailTypeCondition) rightDirectives
                rightChildSelectionSet ∈ pref ++ suffix
                ∧ SelectionEqualUpToReordering
                  (Selection.inlineFragment (some tailTypeCondition)
                    tailDirectives tailChildSelectionSet)
                  (Selection.inlineFragment (some tailTypeCondition)
                    rightDirectives rightChildSelectionSet) := by
        intro tailTypeCondition tailDirectives tailChildSelectionSet htailMem
        rcases hmatch tailTypeCondition tailDirectives
            tailChildSelectionSet (List.mem_cons_of_mem _ htailMem) with
          ⟨matchedDirectives, matchedChildSelectionSet, hmatchedMem,
            hmatchedEq⟩
        have hmatchedMemSplit :
            Selection.inlineFragment (some tailTypeCondition)
              matchedDirectives matchedChildSelectionSet ∈
                pref ++ matchedRight :: suffix := by
          simpa [matchedRight, hrightEq] using hmatchedMem
        have hmatchedMemRest :
            Selection.inlineFragment (some tailTypeCondition)
              matchedDirectives matchedChildSelectionSet ∈ pref ++ suffix := by
          rcases List.mem_append.mp hmatchedMemSplit with hpref | htail
          · exact List.mem_append_left _ hpref
          · rcases List.mem_cons.mp htail with hhead | hsuffix
            · have htypeConditionEq :
                  tailTypeCondition = typeCondition := by
                have hoption :=
                  congrArg inlineFragmentTypeCondition? hhead
                simpa [matchedRight, inlineFragmentTypeCondition?] using hoption
              have htailTypeConditionMem :
                  tailTypeCondition ∈
                    leftRest.filterMap inlineFragmentTypeCondition? :=
                List.mem_filterMap.mpr
                  ⟨Selection.inlineFragment (some tailTypeCondition)
                    tailDirectives tailChildSelectionSet,
                    htailMem, by simp [inlineFragmentTypeCondition?]⟩
              exact False.elim
                (hleftHeadNotRest
                  (by
                    simpa [htypeConditionEq] using htailTypeConditionMem))
            · exact List.mem_append_right _ hsuffix
        exact ⟨matchedDirectives, matchedChildSelectionSet,
          hmatchedMemRest, hmatchedEq⟩
      have htailCoverage :
          ∀ tailTypeCondition,
            tailTypeCondition ∈ (pref ++ suffix).filterMap
                inlineFragmentTypeCondition? ->
              tailTypeCondition ∈
                leftRest.filterMap inlineFragmentTypeCondition? := by
        intro tailTypeCondition htailRightTypeCondition
        rcases List.mem_filterMap.mp htailRightTypeCondition with
          ⟨rightSelection, hrightSelectionRest,
            hrightSelectionTypeCondition⟩
        have hrightSelectionOriginal :
            rightSelection ∈ right := by
          rw [hrightEq]
          rcases List.mem_append.mp hrightSelectionRest with hpref | hsuffix
          · exact List.mem_append_left _ hpref
          · exact List.mem_append_right _
              (List.mem_cons_of_mem _ hsuffix)
        have hrightTypeConditionOriginal :
            tailTypeCondition ∈ right.filterMap inlineFragmentTypeCondition? :=
          List.mem_filterMap.mpr
            ⟨rightSelection, hrightSelectionOriginal,
              hrightSelectionTypeCondition⟩
        have hleftTypeCondition :
            tailTypeCondition ∈
              (Selection.inlineFragment (some typeCondition) directives
                childSelectionSet :: leftRest).filterMap
                inlineFragmentTypeCondition? :=
          hcoverage tailTypeCondition hrightTypeConditionOriginal
        have hleftSplit :
            tailTypeCondition = typeCondition
              ∨ tailTypeCondition ∈
                leftRest.filterMap inlineFragmentTypeCondition? := by
          simpa [inlineFragmentTypeCondition?] using hleftTypeCondition
        rcases hleftSplit with hhead | htail
        · exact False.elim
            (hrightMatchedNotRest
              (by simpa [hhead] using htailRightTypeCondition))
        · exact htail
      rcases ih (pref ++ suffix) hleftRestNodup hrightRestNodup
          hleftRestSome hrightRestSome htailMatch htailCoverage with
        ⟨pairs, hleftPerm, hrightPerm, hpairRelations⟩
      apply SelectionSetEqualUpToReordering.paired
        ((Selection.inlineFragment (some typeCondition) directives
            childSelectionSet, matchedRight) :: pairs)
      · exact hleftPerm.cons
          (Selection.inlineFragment (some typeCondition) directives
            childSelectionSet)
      · have hrightReinsert :
            (matchedRight :: pairs.map Prod.snd).Perm
              (pref ++ matchedRight :: suffix) :=
          (hrightPerm.cons matchedRight).trans List.perm_middle.symm
        simpa [matchedRight, hrightEq] using hrightReinsert
      · intro pair hpair
        rcases List.mem_cons.mp hpair with hhead | htail
        · subst pair
          exact hselectionEq
        · exact hpairRelations pair htail

theorem selectionSetEqualUpToReordering_of_no_normalSelectionSetDiff (schema : Schema)
    : ∀ parentType left right,
        selectionSetDirectiveFree left
        -> selectionSetDirectiveFree right
        -> selectionSetNormal schema parentType left
        -> selectionSetNormal schema parentType right
        -> ¬ NormalSelectionSetDiff schema parentType left right
        -> SelectionSetEqualUpToReordering left right := by
  intro parentType left right hleftFree hrightFree hleftNormal hrightNormal
    hnoDiff
  by_cases hobject : objectTypeNameBool schema parentType = true
  · apply selectionSetEqualUpToReordering_of_field_responseName_matches
    · exact selectionSetNormal_allFields_of_object hleftNormal hobject
    · exact selectionSetNormal_allFields_of_object hrightNormal hobject
    · exact selectionSetNormal_responseNamesNodup hleftNormal
    · exact selectionSetNormal_responseNamesNodup hrightNormal
    · intro responseName fieldName arguments directives childSelectionSet
        hleftMem
      by_cases hrightName :
          responseName ∈ right.filterMap Selection.responseName?
      · rcases selectionSetNormal_field_mem_of_object_responseName_mem
            hrightNormal hobject hrightName with
          ⟨rightFieldName, rightArguments, rightDirectives,
            rightChildSelectionSet, hrightMem⟩
        have hfieldName : fieldName = rightFieldName := by
          by_cases hsame : fieldName = rightFieldName
          · exact hsame
          · exact False.elim
              (hnoDiff
                (NormalSelectionSetDiff.objectFieldName hobject hleftMem
                  hrightMem hsame))
        subst rightFieldName
        have harguments :
            Argument.argumentsEquivalent arguments rightArguments := by
          exact Classical.byContradiction fun hargs =>
            hnoDiff
              (NormalSelectionSetDiff.objectArguments hobject hleftMem
                hrightMem hargs)
        rcases selectionSetNormal_field_child_of_mem_with_returnType
            hleftNormal hleftMem with
          ⟨returnType, hreturnType, hleftChildNormal⟩
        have hleftChildFree :
            selectionSetDirectiveFree childSelectionSet :=
          selectionSetDirectiveFree_field_child_of_mem hleftFree hleftMem
        have hrightChildFree :
            selectionSetDirectiveFree rightChildSelectionSet :=
          selectionSetDirectiveFree_field_child_of_mem hrightFree hrightMem
        have hrightChildNormal :
            selectionSetNormal schema returnType rightChildSelectionSet := by
          rcases selectionSetNormal_field_child_of_mem_with_returnType
              hrightNormal hrightMem with
            ⟨rightReturnType, hrightReturnType, hnormal⟩
          have hsameReturn : rightReturnType = returnType := by
            rw [hreturnType] at hrightReturnType
            exact (Option.some.inj hrightReturnType).symm
          simpa [hsameReturn] using hnormal
        have hchildNoDiff :
            ¬ NormalSelectionSetDiff schema returnType childSelectionSet
                rightChildSelectionSet := by
          intro hchildDiff
          exact hnoDiff
            (NormalSelectionSetDiff.objectChild hobject hreturnType hleftMem
              hrightMem harguments hchildDiff)
        have hchildEq :
            SelectionSetEqualUpToReordering childSelectionSet
              rightChildSelectionSet :=
          selectionSetEqualUpToReordering_of_no_normalSelectionSetDiff schema
            returnType childSelectionSet rightChildSelectionSet
            hleftChildFree hrightChildFree hleftChildNormal hrightChildNormal
            hchildNoDiff
        have hleftDirectives : directives = [] :=
          selectionSetDirectiveFree_field_directives_nil_of_mem hleftFree
            hleftMem
        have hrightDirectives : rightDirectives = [] :=
          selectionSetDirectiveFree_field_directives_nil_of_mem hrightFree
            hrightMem
        subst directives
        subst rightDirectives
        exact ⟨fieldName, rightArguments, [], rightChildSelectionSet,
          hrightMem, SelectionEqualUpToReordering.field responseName fieldName
            [] harguments hchildEq⟩
      · exact False.elim
          (hnoDiff
            (NormalSelectionSetDiff.objectLeftResponseName hobject hleftMem
              hrightName))
    · intro responseName hrightName
      by_cases hleftName :
          responseName ∈ left.filterMap Selection.responseName?
      · exact hleftName
      · rcases selectionSetNormal_field_mem_of_object_responseName_mem
            hrightNormal hobject hrightName with
          ⟨fieldName, arguments, directives, childSelectionSet, hrightMem⟩
        exact False.elim
          (hnoDiff
            (NormalSelectionSetDiff.objectRightResponseName hobject hrightMem
              hleftName))
  · have habstract : objectTypeNameBool schema parentType = false := by
      cases h : objectTypeNameBool schema parentType
      · rfl
      · contradiction
    apply selectionSetEqualUpToReordering_of_inlineFragment_typeCondition_matches
    · exact selectionSetNormal_inlineFragmentTypeConditionsNodup hleftNormal
    · exact selectionSetNormal_inlineFragmentTypeConditionsNodup hrightNormal
    · intro selection hmem
      have hinline :
          Selection.isInlineFragment selection :=
        selectionSetNormal_allInlineFragments_of_abstract hleftNormal
          habstract selection hmem
      cases selection with
      | field responseName fieldName arguments directives childSelectionSet =>
          simp [Selection.isInlineFragment] at hinline
      | inlineFragment maybeTypeCondition directives childSelectionSet =>
          cases maybeTypeCondition with
          | none =>
              rcases hleftNormal with ⟨hground, _hnonRedundant⟩
              unfold selectionSetGroundTyped at hground
              have hselectionGround :=
                hground.2
                  (Selection.inlineFragment none directives childSelectionSet)
                  hmem
              simp [selectionGroundTyped] at hselectionGround
          | some typeCondition =>
              exact ⟨typeCondition, directives, childSelectionSet, rfl⟩
    · intro selection hmem
      have hinline :
          Selection.isInlineFragment selection :=
        selectionSetNormal_allInlineFragments_of_abstract hrightNormal
          habstract selection hmem
      cases selection with
      | field responseName fieldName arguments directives childSelectionSet =>
          simp [Selection.isInlineFragment] at hinline
      | inlineFragment maybeTypeCondition directives childSelectionSet =>
          cases maybeTypeCondition with
          | none =>
              rcases hrightNormal with ⟨hground, _hnonRedundant⟩
              unfold selectionSetGroundTyped at hground
              have hselectionGround :=
                hground.2
                  (Selection.inlineFragment none directives childSelectionSet)
                  hmem
              simp [selectionGroundTyped] at hselectionGround
          | some typeCondition =>
              exact ⟨typeCondition, directives, childSelectionSet, rfl⟩
    · intro typeCondition directives childSelectionSet hleftMem
      by_cases hrightType :
          typeCondition ∈ right.filterMap inlineFragmentTypeCondition?
      · rcases selectionSetNormal_inlineFragment_mem_of_abstract_typeCondition_mem
            hrightNormal habstract hrightType with
          ⟨rightDirectives, rightChildSelectionSet, hrightMem⟩
        rcases selectionSetNormal_inlineFragment_child_of_mem hleftNormal
            hleftMem with
          ⟨_htypeConditionObject, hleftChildNormal⟩
        rcases selectionSetNormal_inlineFragment_child_of_mem hrightNormal
            hrightMem with
          ⟨_hrightTypeConditionObject, hrightChildNormal⟩
        have hleftChildFree :
            selectionSetDirectiveFree childSelectionSet :=
          selectionSetDirectiveFree_inlineFragment_child_of_mem hleftFree
            hleftMem
        have hrightChildFree :
            selectionSetDirectiveFree rightChildSelectionSet :=
          selectionSetDirectiveFree_inlineFragment_child_of_mem hrightFree
            hrightMem
        have hchildNoDiff :
            ¬ NormalSelectionSetDiff schema typeCondition childSelectionSet
                rightChildSelectionSet := by
          intro hchildDiff
          exact hnoDiff
            (NormalSelectionSetDiff.abstractChild habstract hleftMem hrightMem
              hchildDiff)
        have hchildEq :
            SelectionSetEqualUpToReordering childSelectionSet
              rightChildSelectionSet :=
          selectionSetEqualUpToReordering_of_no_normalSelectionSetDiff schema
            typeCondition childSelectionSet rightChildSelectionSet
            hleftChildFree hrightChildFree hleftChildNormal hrightChildNormal
            hchildNoDiff
        have hleftDirectives : directives = [] :=
          selectionSetDirectiveFree_inlineFragment_directives_nil_of_mem
            hleftFree hleftMem
        have hrightDirectives : rightDirectives = [] :=
          selectionSetDirectiveFree_inlineFragment_directives_nil_of_mem
            hrightFree hrightMem
        subst directives
        subst rightDirectives
        exact ⟨[], rightChildSelectionSet, hrightMem,
          SelectionEqualUpToReordering.inlineFragment (some typeCondition) []
            hchildEq⟩
      · exact False.elim
          (hnoDiff
            (NormalSelectionSetDiff.abstractLeftTypeCondition habstract
              hleftMem hrightType))
    · intro typeCondition hrightType
      by_cases hleftType :
          typeCondition ∈ left.filterMap inlineFragmentTypeCondition?
      · exact hleftType
      · rcases selectionSetNormal_inlineFragment_mem_of_abstract_typeCondition_mem
            hrightNormal habstract hrightType with
          ⟨directives, childSelectionSet, hrightMem⟩
        exact False.elim
          (hnoDiff
            (NormalSelectionSetDiff.abstractRightTypeCondition habstract
              hrightMem hleftType))
termination_by _parentType left right =>
  SelectionSet.size left + SelectionSet.size right
decreasing_by
  all_goals
    first
    | have hleftLt :=
        selectionSet_size_field_child_lt_of_mem (selectionSet := left) hleftMem
      have hrightLt :=
        selectionSet_size_field_child_lt_of_mem (selectionSet := right) hrightMem
      omega
    | have hleftLt :=
        selectionSet_size_inlineFragment_child_lt_of_mem
          (selectionSet := left) hleftMem
      have hrightLt :=
        selectionSet_size_inlineFragment_child_lt_of_mem
          (selectionSet := right) hrightMem
      omega

theorem normalSelectionSetDiff_of_not_equalUpToReordering
    {schema : Schema} {parentType : Name} {left right : List Selection}
    : selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> ¬ SelectionSetEqualUpToReordering left right
      -> NormalSelectionSetDiff schema parentType left right := by
  intro hleftFree hrightFree hleftNormal hrightNormal hnotEqual
  exact Classical.byContradiction fun hnoDiff =>
    hnotEqual
      (selectionSetEqualUpToReordering_of_no_normalSelectionSetDiff schema
        parentType left right hleftFree hrightFree hleftNormal hrightNormal
        hnoDiff)

end GroundTypeNormalization

end NormalForm

end GraphQL
