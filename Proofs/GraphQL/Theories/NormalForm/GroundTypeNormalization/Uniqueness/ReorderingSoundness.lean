import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.ExecutionKeys
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.ExecutionResponseKeys
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.Readiness

/-!
Semantic soundness of normal-form equality up to sibling reordering.

Raw `SelectionSetEqualUpToReordering` is not sound for permissive syntax: reordering
two fields with the same response name can change which field heads the collected
group. Normal selection sets exclude that case. This module proves soundness in the
directive-free normal-form scope used by the public uniqueness theorems.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

namespace ReorderingSoundness

open Execution

def ResponseValueResultEquivalent (left right : Result ResponseValue) : Prop :=
  match left, right with
  | .error leftErrors, .error rightErrors => leftErrors = rightErrors
  | .ok (leftValue, leftErrors), .ok (rightValue, rightErrors) =>
      ResponseValue.semanticEquivalent leftValue rightValue ∧ leftErrors = rightErrors
  | _, _ => False

def ListResponseValueResultEquivalent (left right : Result (List ResponseValue)) : Prop :=
  match left, right with
  | .error leftErrors, .error rightErrors => leftErrors = rightErrors
  | .ok (leftValues, leftErrors), .ok (rightValues, rightErrors) =>
      ResponseValue.canonicalList leftValues = ResponseValue.canonicalList rightValues
      ∧ leftErrors = rightErrors
  | _, _ => False

def SelectionSetResultEquivalent (left right : Result (List (Name × ResponseValue)))
    : Prop :=
  match left, right with
  | .error leftErrors, .error rightErrors => leftErrors = rightErrors
  | .ok (leftFields, leftErrors), .ok (rightFields, rightErrors) =>
      ResponseValue.semanticEquivalent (.object leftFields) (.object rightFields)
      ∧ leftErrors = rightErrors
  | _, _ => False

theorem responseValue_semanticEquivalent_refl (value : ResponseValue)
    : ResponseValue.semanticEquivalent value value := by
  rfl

theorem responseValue_semanticEquivalent_symm {left right : ResponseValue}
    : ResponseValue.semanticEquivalent left right
      -> ResponseValue.semanticEquivalent right left := by
  exact Eq.symm

theorem responseValue_semanticEquivalent_trans {left middle right : ResponseValue}
    : ResponseValue.semanticEquivalent left middle
      -> ResponseValue.semanticEquivalent middle right
      -> ResponseValue.semanticEquivalent left right := by
  exact Eq.trans

theorem responseValueResultEquivalent_of_eq {left right : Result ResponseValue}
    : left = right -> ResponseValueResultEquivalent left right := by
  intro heq
  subst right
  cases left with
  | error _errors => rfl
  | ok result =>
      rcases result with ⟨value, errors⟩
      exact ⟨responseValue_semanticEquivalent_refl value, rfl⟩

theorem selectionSetResultEquivalent_of_eq
    {left right : Result (List (Name × ResponseValue))}
    : left = right -> SelectionSetResultEquivalent left right := by
  intro heq
  subst right
  cases left with
  | error _errors => rfl
  | ok result =>
      rcases result with ⟨fields, errors⟩
      exact ⟨responseValue_semanticEquivalent_refl (.object fields), rfl⟩

private def responseFieldLE (left right : Name × ResponseValue) : Prop :=
  left.1 ≤ right.1

private theorem insertObjectFieldSorted_perm (field : Name × ResponseValue)
    : ∀ fields,
        (ResponseValue.insertObjectFieldSorted field fields).Perm (field :: fields)
  | [] => List.Perm.refl _
  | candidate :: rest => by
      by_cases hle : field.1 ≤ candidate.1
      · simp [ResponseValue.insertObjectFieldSorted, hle]
      · rw [ResponseValue.insertObjectFieldSorted]
        simp only [hle, if_false]
        exact
          ((insertObjectFieldSorted_perm field rest).cons candidate).trans
            (List.Perm.swap field candidate rest)

private theorem sortObjectFieldsByName_perm
    : ∀ fields, (ResponseValue.sortObjectFieldsByName fields).Perm fields
  | [] => List.Perm.refl _
  | field :: rest => by
      exact
        (insertObjectFieldSorted_perm field
          (ResponseValue.sortObjectFieldsByName rest)).trans
          ((sortObjectFieldsByName_perm rest).cons field)

private theorem responseFieldLE_trans {first second third : Name × ResponseValue}
    : responseFieldLE first second
      -> responseFieldLE second third
      -> responseFieldLE first third := by
  exact String.le_trans

private theorem insertObjectFieldSorted_pairwise (field : Name × ResponseValue)
    : ∀ fields,
        List.Pairwise responseFieldLE fields
        -> List.Pairwise responseFieldLE
            (ResponseValue.insertObjectFieldSorted field fields)
  | [], _hsorted => by
      simp [ResponseValue.insertObjectFieldSorted]
  | candidate :: rest, hsorted => by
      have hcandidateRest :
          ∀ restField ∈ rest, responseFieldLE candidate restField :=
        (List.pairwise_cons.mp hsorted).1
      have hrestSorted : List.Pairwise responseFieldLE rest :=
        (List.pairwise_cons.mp hsorted).2
      by_cases hle : field.1 ≤ candidate.1
      · rw [ResponseValue.insertObjectFieldSorted]
        simp only [hle, if_true]
        apply List.pairwise_cons.mpr
        constructor
        · intro restField hmem
          rcases List.mem_cons.mp hmem with hhead | htail
          · subst restField
            exact hle
          · exact responseFieldLE_trans hle
              (hcandidateRest restField htail)
        · exact hsorted
      · rw [ResponseValue.insertObjectFieldSorted]
        simp only [hle, if_false]
        apply List.pairwise_cons.mpr
        constructor
        · intro restField hmem
          have hcandidateField : candidate.1 ≤ field.1 :=
            (String.le_total field.1 candidate.1).resolve_left hle
          have hmem' :
              restField = field ∨ restField ∈ rest :=
            (ResponseKeys.ResponseValue.mem_insertObjectFieldSorted_iff
              field restField rest).mp hmem
          rcases hmem' with hfield | hrest
          · subst restField
            exact hcandidateField
          · exact hcandidateRest restField hrest
        · exact insertObjectFieldSorted_pairwise field rest hrestSorted

private theorem sortObjectFieldsByName_pairwise
    : ∀ fields,
        List.Pairwise responseFieldLE (ResponseValue.sortObjectFieldsByName fields)
  | [] => by simp [ResponseValue.sortObjectFieldsByName]
  | field :: rest => by
      exact insertObjectFieldSorted_pairwise field
        (ResponseValue.sortObjectFieldsByName rest)
        (sortObjectFieldsByName_pairwise rest)

private theorem pair_eq_of_same_key_of_mem_nodup
    {left right : List (Name × ResponseValue)}
    (hnodup : (left.map Prod.fst).Nodup)
    {first second : Name × ResponseValue}
    : first ∈ left
      -> second ∈ right
      -> left.Perm right
      -> first.1 = second.1
      -> first = second := by
  intro hfirst hsecond hperm hkeys
  have hsecondLeft : second ∈ left := hperm.mem_iff.mpr hsecond
  have unique :
      ∀ (fields : List (Name × ResponseValue)),
        (fields.map Prod.fst).Nodup ->
        ∀ {first second : Name × ResponseValue},
          first ∈ fields ->
          second ∈ fields ->
          first.1 = second.1 ->
            first = second := by
    intro fields
    induction fields with
    | nil =>
        intro _hnodup first second hfirst _hsecond _hkeys
        simp at hfirst
    | cons head rest ih =>
        intro hfieldsNodup first second hfirst hsecond hsameKey
        have hheadNotRest : head.1 ∉ rest.map Prod.fst :=
          (List.nodup_cons.mp hfieldsNodup).1
        have hrestNodup : (rest.map Prod.fst).Nodup :=
          (List.nodup_cons.mp hfieldsNodup).2
        rcases List.mem_cons.mp hfirst with hfirstHead | hfirstRest
        · subst first
          rcases List.mem_cons.mp hsecond with hsecondHead | hsecondRest
          · exact hsecondHead.symm
          · exact False.elim
              (hheadNotRest (List.mem_map.mpr
                ⟨second, hsecondRest, hsameKey.symm⟩))
        · rcases List.mem_cons.mp hsecond with hsecondHead | hsecondRest
          · subst second
            exact False.elim
              (hheadNotRest (List.mem_map.mpr
                ⟨first, hfirstRest, hsameKey⟩))
          · exact ih hrestNodup hfirstRest hsecondRest hsameKey
  exact unique left hnodup hfirst hsecondLeft hkeys

private theorem sortObjectFieldsByName_eq_of_perm_nodup
    {left right : List (Name × ResponseValue)}
    (hperm : left.Perm right)
    (hnodup : (left.map Prod.fst).Nodup)
    : ResponseValue.sortObjectFieldsByName left
      = ResponseValue.sortObjectFieldsByName right := by
  apply List.Perm.eq_of_pairwise
  · intro first second hfirst hsecond hfirstSecond hsecondFirst
    apply pair_eq_of_same_key_of_mem_nodup hnodup
    · exact (sortObjectFieldsByName_perm left).mem_iff.mp hfirst
    · exact (sortObjectFieldsByName_perm right).mem_iff.mp hsecond
    · exact hperm
    · exact String.le_antisymm hfirstSecond hsecondFirst
  · exact sortObjectFieldsByName_pairwise left
  · exact sortObjectFieldsByName_pairwise right
  · exact
      (sortObjectFieldsByName_perm left).trans
        (hperm.trans (sortObjectFieldsByName_perm right).symm)

theorem semanticEquivalent_object_of_canonical_fields_perm_nodup
    {left right : List (Name × ResponseValue)}
    (hperm
      : (ResponseValue.canonicalObjectFields left).Perm
          (ResponseValue.canonicalObjectFields right))
    (hnodup : (left.map Prod.fst).Nodup)
    : ResponseValue.semanticEquivalent (.object left) (.object right) := by
  unfold ResponseValue.semanticEquivalent ResponseValue.canonical
  apply congrArg ResponseValue.object
  apply sortObjectFieldsByName_eq_of_perm_nodup hperm
  simpa [ResponseKeys.ResponseValue.canonicalObjectFields_map_fst] using
    hnodup

theorem responseValue_semanticEquivalent_object_cons
    {name : Name} {leftValue rightValue : ResponseValue}
    {leftFields rightFields : List (Name × ResponseValue)}
    : ResponseValue.semanticEquivalent leftValue rightValue
      -> ResponseValue.semanticEquivalent (.object leftFields) (.object rightFields)
      -> ResponseValue.semanticEquivalent
          (.object ((name, leftValue) :: leftFields))
          (.object ((name, rightValue) :: rightFields)) := by
  intro hvalue hfields
  unfold ResponseValue.semanticEquivalent at hvalue hfields ⊢
  simp only [ResponseValue.canonical] at hfields ⊢
  injection hfields with hfields'
  simp [ResponseValue.canonicalObjectFields,
    ResponseValue.sortObjectFieldsByName, hvalue, hfields']

theorem responseValueResultEquivalent_nonNullCompletion
    {left right : Result ResponseValue}
    : ResponseValueResultEquivalent left right
      -> ResponseValueResultEquivalent
          (nonNullCompletion left) (nonNullCompletion right) := by
  intro hequivalent
  cases left with
  | error leftErrors =>
      cases right with
      | error rightErrors =>
          simpa [ResponseValueResultEquivalent, nonNullCompletion]
            using hequivalent
      | ok rightResult =>
          simp [ResponseValueResultEquivalent] at hequivalent
  | ok leftResult =>
      cases right with
      | error rightErrors =>
          simp [ResponseValueResultEquivalent] at hequivalent
      | ok rightResult =>
          rcases leftResult with ⟨leftValue, leftErrors⟩
          rcases rightResult with ⟨rightValue, rightErrors⟩
          rcases hequivalent with ⟨hvalue, herrors⟩
          subst rightErrors
          cases leftValue <;> cases rightValue <;>
            simp [ResponseValueResultEquivalent, nonNullCompletion,
              ResponseValue.semanticEquivalent, ResponseValue.canonical]
              at hvalue ⊢
          all_goals exact hvalue

theorem listResponseValueResultEquivalent_catchBubbleAsNull
    {left right : Result (List ResponseValue)}
    : ListResponseValueResultEquivalent left right
      -> ResponseValueResultEquivalent
          (catchBubbleAsNull ResponseValue.list left)
          (catchBubbleAsNull ResponseValue.list right) := by
  intro hequivalent
  cases left <;> cases right <;>
    simp [ListResponseValueResultEquivalent,
      ResponseValueResultEquivalent, catchBubbleAsNull,
      ResponseValue.semanticEquivalent, ResponseValue.canonical] at hequivalent ⊢
  all_goals exact hequivalent

theorem selectionSetResultEquivalent_catchBubbleAsNull
    {left right : Result (List (Name × ResponseValue))}
    : SelectionSetResultEquivalent left right
      -> ResponseValueResultEquivalent
          (catchBubbleAsNull ResponseValue.object left)
          (catchBubbleAsNull ResponseValue.object right) := by
  intro hequivalent
  cases left <;> cases right <;>
    simp [SelectionSetResultEquivalent,
      ResponseValueResultEquivalent, catchBubbleAsNull,
      ResponseValue.semanticEquivalent, ResponseValue.canonical] at hequivalent ⊢
  all_goals assumption

theorem listResponseValueResultEquivalent_combine_cons
    {leftHead rightHead : Result ResponseValue}
    {leftTail rightTail : Result (List ResponseValue)}
    : ResponseValueResultEquivalent leftHead rightHead
      -> ListResponseValueResultEquivalent leftTail rightTail
      -> ListResponseValueResultEquivalent
          (Result.combine List.cons leftHead leftTail)
          (Result.combine List.cons rightHead rightTail) := by
  intro hhead htail
  cases leftHead <;> cases rightHead <;>
    cases leftTail <;> cases rightTail <;>
    simp [ResponseValueResultEquivalent,
      ListResponseValueResultEquivalent, Result.combine] at hhead htail ⊢
  all_goals try omega
  rename_i leftHeadResult rightHeadResult leftTailResult rightTailResult
  rcases leftHeadResult with ⟨leftValue, leftHeadErrors⟩
  rcases rightHeadResult with ⟨rightValue, rightHeadErrors⟩
  rcases leftTailResult with ⟨leftValues, leftTailErrors⟩
  rcases rightTailResult with ⟨rightValues, rightTailErrors⟩
  rcases hhead with ⟨hheadData, hheadErrors⟩
  rcases htail with ⟨htailData, htailErrors⟩
  change ResponseValue.canonical leftValue =
    ResponseValue.canonical rightValue at hheadData
  constructor
  · simp [ResponseValue.canonicalList, hheadData, htailData]
  · omega

theorem selectionSetResultEquivalent_symm
    {left right : Result (List (Name × ResponseValue))}
    : SelectionSetResultEquivalent left right
      -> SelectionSetResultEquivalent right left := by
  intro hequivalent
  cases left with
  | error leftErrors =>
      cases right with
      | error rightErrors =>
          simpa [SelectionSetResultEquivalent] using hequivalent.symm
      | ok rightResult =>
          simp [SelectionSetResultEquivalent] at hequivalent
  | ok leftResult =>
      cases right with
      | error rightErrors =>
          simp [SelectionSetResultEquivalent] at hequivalent
      | ok rightResult =>
          rcases hequivalent with ⟨hdata, herrors⟩
          exact ⟨responseValue_semanticEquivalent_symm hdata, herrors.symm⟩

theorem selectionSetResultEquivalent_trans
    {left middle right : Result (List (Name × ResponseValue))}
    : SelectionSetResultEquivalent left middle
      -> SelectionSetResultEquivalent middle right
      -> SelectionSetResultEquivalent left right := by
  intro hleft hright
  cases left with
  | error leftErrors =>
      cases middle with
      | error middleErrors =>
          cases right with
          | error rightErrors =>
              exact hleft.trans hright
          | ok rightResult =>
              simp [SelectionSetResultEquivalent] at hright
      | ok middleResult =>
          simp [SelectionSetResultEquivalent] at hleft
  | ok leftResult =>
      cases middle with
      | error middleErrors =>
          simp [SelectionSetResultEquivalent] at hleft
      | ok middleResult =>
          cases right with
          | error rightErrors =>
              simp [SelectionSetResultEquivalent] at hright
          | ok rightResult =>
              exact
                ⟨responseValue_semanticEquivalent_trans hleft.1 hright.1,
                  hleft.2.trans hright.2⟩

private def fieldGroupOfSelection (executionParentType : Name)
    : Selection -> Name × List ExecutableField
  | .field responseName fieldName arguments _directives childSelectionSet =>
      (
        responseName,
        [{
          parentType := executionParentType
          responseName := responseName
          fieldName := fieldName
          arguments := arguments
          selectionSet := childSelectionSet
        }]
      )
  | .inlineFragment _typeCondition _directives _childSelectionSet =>
      ("", [])

theorem collectFields_allFields_directiveFree_nodup_eq_map
    {ObjectRef : Type}
    (schema : Schema) (variableValues : VariableValues)
    (executionParentType : Name) (source : ResolverValue ObjectRef)
    : ∀ selectionSet,
        selectionsAllFields selectionSet
        -> selectionSetDirectiveFree selectionSet
        -> responseNamesNodup selectionSet
        -> collectFields schema variableValues executionParentType source selectionSet
            = selectionSet.map (fieldGroupOfSelection executionParentType)
  | [], _hallFields, _hfree, _hnodup => by
      simp [collectFields]
  | selection :: rest, hallFields, hfree, hnodup => by
      have hselectionField : Selection.isField selection :=
        hallFields selection (by simp)
      cases selection with
      | inlineFragment typeCondition directives childSelectionSet =>
          simp [Selection.isField] at hselectionField
      | field responseName fieldName arguments directives childSelectionSet =>
          have hdirectives : directives = [] :=
            (selectionSetDirectiveFree_head hfree).1
          subst directives
          have hnames :
              (responseName ::
                rest.filterMap Selection.responseName?).Nodup := by
            simpa [responseNamesNodup, Selection.responseName?] using hnodup
          have hrestAll : selectionsAllFields rest :=
            selectionsAllFields_tail hallFields
          have hrestFree : selectionSetDirectiveFree rest :=
            selectionSetDirectiveFree_tail hfree
          have hrestNodup : responseNamesNodup rest := by
            simpa [responseNamesNodup] using (List.nodup_cons.mp hnames).2
          have hnotCollect :
              responseName ∉
                (collectFields schema variableValues executionParentType
                  source rest).map Prod.fst := by
            intro hmem
            have hresponseNameMem :
                responseName ∈ rest.filterMap Selection.responseName? :=
              (ExecutionKeys.collectFields_allFields_directiveFree_key_mem_iff
                schema variableValues executionParentType source responseName
                rest hrestAll hrestFree).mp hmem
            exact (List.nodup_cons.mp hnames).1 hresponseNameMem
          rw [collectFields_field_noDirectives_cons_of_responseName_not_mem
            schema variableValues executionParentType source responseName
            fieldName arguments childSelectionSet rest hnotCollect]
          rw [collectFields_allFields_directiveFree_nodup_eq_map schema
            variableValues executionParentType source rest hrestAll hrestFree
            hrestNodup]
          rfl

theorem selectionSetEqualUpToReordering_left_mem
    {left right : List Selection} {leftSelection : Selection}
    : SelectionSetEqualUpToReordering left right
      -> leftSelection ∈ left
      -> ∃ rightSelection,
          rightSelection ∈ right
          ∧ SelectionEqualUpToReordering leftSelection rightSelection := by
  intro hequal hleftMem
  rcases hequal with ⟨pairs, hleft, hright, hrelations⟩
  have hleftPair : leftSelection ∈ pairs.map Prod.fst :=
    hleft.mem_iff.mpr hleftMem
  rcases List.mem_map.mp hleftPair with
    ⟨pair, hpairMem, hpairLeft⟩
  have hrightPair : pair.2 ∈ pairs.map Prod.snd :=
    List.mem_map.mpr ⟨pair, hpairMem, rfl⟩
  exact
    ⟨pair.2, hright.mem_iff.mp hrightPair,
      hpairLeft ▸ hrelations pair hpairMem⟩

theorem selectionSetEqualUpToReordering_right_mem
    {left right : List Selection} {rightSelection : Selection}
    : SelectionSetEqualUpToReordering left right
      -> rightSelection ∈ right
      -> ∃ leftSelection,
          leftSelection ∈ left
          ∧ SelectionEqualUpToReordering leftSelection rightSelection := by
  intro hequal hrightMem
  rcases hequal with ⟨pairs, hleft, hright, hrelations⟩
  have hrightPair : rightSelection ∈ pairs.map Prod.snd :=
    hright.mem_iff.mpr hrightMem
  rcases List.mem_map.mp hrightPair with
    ⟨pair, hpairMem, hpairRight⟩
  have hleftPair : pair.1 ∈ pairs.map Prod.fst :=
    List.mem_map.mpr ⟨pair, hpairMem, rfl⟩
  exact
    ⟨pair.1, hleft.mem_iff.mp hleftPair,
      hpairRight ▸ hrelations pair hpairMem⟩

theorem inlineFragmentTypeCondition_mem_iff_of_equalUpToReordering
    {left right : List Selection} {typeCondition : Name}
    : SelectionSetEqualUpToReordering left right
      -> (typeCondition ∈ left.filterMap inlineFragmentTypeCondition?
          ↔ typeCondition ∈ right.filterMap inlineFragmentTypeCondition?) := by
  intro hequal
  constructor
  · intro hleftCondition
    rcases List.mem_filterMap.mp hleftCondition with
      ⟨leftSelection, hleftMem, hleftConditionValue⟩
    rcases selectionSetEqualUpToReordering_left_mem hequal hleftMem with
      ⟨rightSelection, hrightMem, hrelation⟩
    cases hrelation with
    | field responseName fieldName directives harguments hchildren =>
        simp [inlineFragmentTypeCondition?] at hleftConditionValue
    | inlineFragment maybeTypeCondition directives hchildren =>
        cases maybeTypeCondition with
        | none =>
            simp [inlineFragmentTypeCondition?] at hleftConditionValue
        | some matchedTypeCondition =>
            exact List.mem_filterMap.mpr
              ⟨_, hrightMem, by
                simpa [inlineFragmentTypeCondition?] using
                  hleftConditionValue⟩
  · intro hrightCondition
    rcases List.mem_filterMap.mp hrightCondition with
      ⟨rightSelection, hrightMem, hrightConditionValue⟩
    rcases selectionSetEqualUpToReordering_right_mem hequal hrightMem with
      ⟨leftSelection, hleftMem, hrelation⟩
    cases hrelation with
    | field responseName fieldName directives harguments hchildren =>
        simp [inlineFragmentTypeCondition?] at hrightConditionValue
    | inlineFragment maybeTypeCondition directives hchildren =>
        cases maybeTypeCondition with
        | none =>
            simp [inlineFragmentTypeCondition?] at hrightConditionValue
        | some matchedTypeCondition =>
            exact List.mem_filterMap.mpr
              ⟨_, hleftMem, by
                simpa [inlineFragmentTypeCondition?] using
                  hrightConditionValue⟩

private theorem fields_eq_singleton_of_map_fst_eq_singleton
    {fields : List (Name × ResponseValue)} {name : Name}
    : fields.map Prod.fst = [name] -> ∃ value, fields = [(name, value)] := by
  intro hkeys
  cases fields with
  | nil => simp at hkeys
  | cons field rest =>
      cases rest with
      | nil =>
          rcases field with ⟨fieldName, value⟩
          simp at hkeys
          subst fieldName
          exact ⟨value, rfl⟩
      | cons second tail =>
          simp at hkeys

private theorem canonicalObjectFields_perm {left right : List (Name × ResponseValue)}
    : left.Perm right
      -> (ResponseValue.canonicalObjectFields left).Perm
          (ResponseValue.canonicalObjectFields right) := by
  intro hperm
  induction hperm with
  | nil => exact List.Perm.nil
  | cons field hperm ih =>
      rcases field with ⟨name, value⟩
      simpa [ResponseValue.canonicalObjectFields] using
        ih.cons (name, ResponseValue.canonical value)
  | swap first second rest =>
      rcases first with ⟨firstName, firstValue⟩
      rcases second with ⟨secondName, secondValue⟩
      simpa [ResponseValue.canonicalObjectFields] using
        List.Perm.swap
          (firstName, ResponseValue.canonical firstValue)
          (secondName, ResponseValue.canonical secondValue)
          (ResponseValue.canonicalObjectFields rest)
  | trans _ _ ihleft ihright => exact ihleft.trans ihright

private theorem executeCollectedFields_cons_equivalent
    {ObjectRef : Type}
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (fuel : Nat)
    (source : ResolverValue ObjectRef)
    (responseName : Name)
    (leftFields rightFields : List ExecutableField)
    (leftTail rightTail : List (Name × List ExecutableField))
    : SelectionSetResultEquivalent
        (executeField schema resolvers variableValues fuel source responseName leftFields)
        (executeField schema resolvers variableValues fuel source responseName
          rightFields)
      -> SelectionSetResultEquivalent
          (executeCollectedFields schema resolvers variableValues fuel source leftTail)
          (executeCollectedFields schema resolvers variableValues fuel source rightTail)
      -> SelectionSetResultEquivalent
          (executeCollectedFields schema resolvers variableValues fuel source
            ((responseName, leftFields) :: leftTail))
          (executeCollectedFields schema resolvers variableValues fuel source
            ((responseName, rightFields) :: rightTail)) := by
  intro hhead htail
  cases hleftHead :
      executeField schema resolvers variableValues fuel source responseName
        leftFields <;>
    cases hrightHead :
      executeField schema resolvers variableValues fuel source responseName
        rightFields <;>
    cases hleftTail :
      executeCollectedFields schema resolvers variableValues fuel source
        leftTail <;>
    cases hrightTail :
      executeCollectedFields schema resolvers variableValues fuel source
        rightTail <;>
    simp [executeCollectedFields, hleftHead, hrightHead, hleftTail,
      hrightTail, Result.combine, SelectionSetResultEquivalent] at hhead htail ⊢
  all_goals try omega
  rename_i leftHeadResult rightHeadResult leftTailResult rightTailResult
  rcases leftHeadResult with ⟨leftHeadOutput, leftHeadErrors⟩
  rcases rightHeadResult with ⟨rightHeadOutput, rightHeadErrors⟩
  rcases leftTailResult with ⟨leftTailOutput, leftTailErrors⟩
  rcases rightTailResult with ⟨rightTailOutput, rightTailErrors⟩
  rcases fields_eq_singleton_of_map_fst_eq_singleton
      (ExecutionResponseKeys.executeField_ok_keys schema resolvers
        variableValues fuel source responseName leftFields hleftHead) with
    ⟨leftValue, hleftOutput⟩
  rcases fields_eq_singleton_of_map_fst_eq_singleton
      (ExecutionResponseKeys.executeField_ok_keys schema resolvers
        variableValues fuel source responseName rightFields hrightHead) with
    ⟨rightValue, hrightOutput⟩
  subst leftHeadOutput
  subst rightHeadOutput
  rcases hhead with ⟨hheadData, hheadErrors⟩
  rcases htail with ⟨htailData, htailErrors⟩
  have hvalue :
      ResponseValue.semanticEquivalent leftValue rightValue := by
    simpa [ResponseValue.semanticEquivalent, ResponseValue.canonical,
      ResponseValue.canonicalObjectFields,
      ResponseValue.sortObjectFieldsByName,
      ResponseValue.insertObjectFieldSorted] using hheadData
  constructor
  · simpa using
      responseValue_semanticEquivalent_object_cons hvalue htailData
  · omega

theorem executeCollectedFields_equivalent_of_perm
    {ObjectRef : Type}
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (fuel : Nat)
    (source : ResolverValue ObjectRef)
    {left right : List (Name × List ExecutableField)}
    : left.Perm right
      -> (left.map Prod.fst).Nodup
      -> SelectionSetResultEquivalent
          (executeCollectedFields schema resolvers variableValues fuel source left)
          (executeCollectedFields schema resolvers variableValues fuel source right) := by
  intro hperm
  induction hperm with
  | nil =>
      intro _hnodup
      exact selectionSetResultEquivalent_of_eq rfl
  | cons group hperm ih =>
      intro hnodup
      apply executeCollectedFields_cons_equivalent schema resolvers
        variableValues fuel source group.1 group.2 group.2 _ _
      · exact selectionSetResultEquivalent_of_eq rfl
      · exact ih (List.nodup_cons.mp hnodup).2
  | swap first second rest =>
      intro hnodup
      rcases first with ⟨firstName, firstFields⟩
      rcases second with ⟨secondName, secondFields⟩
      simp only [executeCollectedFields]
      cases hfirst :
          executeField schema resolvers variableValues fuel source firstName
            firstFields <;>
        cases hsecond :
          executeField schema resolvers variableValues fuel source secondName
            secondFields <;>
        cases htail :
          executeCollectedFields schema resolvers variableValues fuel source
            rest <;>
        simp [Result.combine, SelectionSetResultEquivalent]
      all_goals try omega
      rename_i firstResult secondResult tailResult
      rcases firstResult with ⟨firstOutput, firstErrors⟩
      rcases secondResult with ⟨secondOutput, secondErrors⟩
      rcases tailResult with ⟨tailOutput, tailErrors⟩
      have houtputPerm :
          (secondOutput ++ (firstOutput ++ tailOutput)).Perm
            (firstOutput ++ (secondOutput ++ tailOutput)) := by
        simpa [List.append_assoc] using
          (List.Perm.append_right tailOutput
            (List.perm_append_comm (l₁ := secondOutput)
              (l₂ := firstOutput)))
      have hcanonicalPerm :
          (ResponseValue.canonicalObjectFields
              (secondOutput ++ (firstOutput ++ tailOutput))).Perm
            (ResponseValue.canonicalObjectFields
              (firstOutput ++ (secondOutput ++ tailOutput))) :=
        canonicalObjectFields_perm houtputPerm
      have hfirstKeys :=
        ExecutionResponseKeys.executeField_ok_keys schema resolvers
          variableValues fuel source firstName firstFields hfirst
      have hsecondKeys :=
        ExecutionResponseKeys.executeField_ok_keys schema resolvers
          variableValues fuel source secondName secondFields hsecond
      have htailKeys :=
        ExecutionResponseKeys.executeCollectedFields_ok_keys schema resolvers
          variableValues fuel source rest tailOutput tailErrors htail
      have houtputKeys :
          (secondOutput ++ (firstOutput ++ tailOutput)).map Prod.fst =
            ((secondName, secondFields) ::
              (firstName, firstFields) :: rest).map Prod.fst := by
        simp [List.map_append, hfirstKeys, hsecondKeys, htailKeys]
      have houtputNodup :
          ((secondOutput ++ (firstOutput ++ tailOutput)).map Prod.fst).Nodup :=
        houtputKeys ▸ hnodup
      constructor
      · exact semanticEquivalent_object_of_canonical_fields_perm_nodup
          hcanonicalPerm houtputNodup
      · omega
  | trans leftMiddle middleRight ihleft ihright =>
      intro hnodup
      have hmiddleNodup :
          (List.map Prod.fst _).Nodup :=
        ((leftMiddle.map Prod.fst).nodup_iff).mp hnodup
      exact selectionSetResultEquivalent_trans
        (ihleft hnodup) (ihright hmiddleNodup)

def CompleteValueSoundAtFuel (fuel : Nat) : Prop :=
  ∀ {ObjectRef : Type}
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues)
      (executionParentType responseName fieldName : Name)
      (leftArguments rightArguments : List Argument)
      (leftChild rightChild : List Selection)
      (normalChildParentType : Name)
      (fieldType : TypeRef) (value : ResolverValue ObjectRef),
    Argument.argumentsEquivalent leftArguments rightArguments
    -> selectionSetDirectiveFree leftChild
    -> selectionSetDirectiveFree rightChild
    -> selectionSetNormal schema normalChildParentType leftChild
    -> selectionSetNormal schema normalChildParentType rightChild
    -> SelectionSetEqualUpToReordering leftChild rightChild
    -> ResponseValueResultEquivalent
        (completeValue schema resolvers variableValues fuel fieldType
          [{
            parentType := executionParentType
            responseName := responseName
            fieldName := fieldName
            arguments := leftArguments
            selectionSet := leftChild
          }] value)
        (completeValue schema resolvers variableValues fuel fieldType
          [{
            parentType := executionParentType
            responseName := responseName
            fieldName := fieldName
            arguments := rightArguments
            selectionSet := rightChild
          }] value)

def SelectionSetSoundAtFuel (fuel : Nat) : Prop :=
  ∀ {ObjectRef : Type}
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues)
      (normalParentType executionParentType runtimeType : Name)
      (ref : ObjectRef) (left right : List Selection),
    selectionSetDirectiveFree left
    -> selectionSetDirectiveFree right
    -> selectionSetNormal schema normalParentType left
    -> selectionSetNormal schema normalParentType right
    -> SelectionSetEqualUpToReordering left right
    -> (objectTypeNameBool schema normalParentType = true
        ∨ executionParentType = normalParentType
        ∨ executionParentType = runtimeType)
    -> SelectionSetResultEquivalent
        (executeSelectionSet schema resolvers variableValues fuel
          executionParentType (.object runtimeType ref) left)
        (executeSelectionSet schema resolvers variableValues fuel
          executionParentType (.object runtimeType ref) right)

def SingletonFieldSoundAtFuel (fuel : Nat) : Prop :=
  ∀ {ObjectRef : Type}
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues) (source : ResolverValue ObjectRef)
      (responseName executionParentType fieldName : Name)
      (leftArguments rightArguments : List Argument)
      (leftChild rightChild : List Selection)
      (normalChildParentType : Name),
    Argument.argumentsEquivalent leftArguments rightArguments
    -> selectionSetDirectiveFree leftChild
    -> selectionSetDirectiveFree rightChild
    -> selectionSetNormal schema normalChildParentType leftChild
    -> selectionSetNormal schema normalChildParentType rightChild
    -> SelectionSetEqualUpToReordering leftChild rightChild
    -> SelectionSetResultEquivalent
        (executeField schema resolvers variableValues fuel source responseName
          [{
            parentType := executionParentType
            responseName := responseName
            fieldName := fieldName
            arguments := leftArguments
            selectionSet := leftChild
          }])
        (executeField schema resolvers variableValues fuel source responseName
          [{
            parentType := executionParentType
            responseName := responseName
            fieldName := fieldName
            arguments := rightArguments
            selectionSet := rightChild
          }])

theorem selectionSetResultEquivalent_singleFieldResult
    {responseName : Name} {left right : Result ResponseValue}
    : ResponseValueResultEquivalent left right
      -> SelectionSetResultEquivalent
          (singleFieldResult responseName left)
          (singleFieldResult responseName right) := by
  intro hequivalent
  cases left with
  | error leftErrors =>
      cases right with
      | error rightErrors =>
          simpa [ResponseValueResultEquivalent,
            SelectionSetResultEquivalent, singleFieldResult]
            using hequivalent
      | ok rightResult =>
          simp [ResponseValueResultEquivalent] at hequivalent
  | ok leftResult =>
      cases right with
      | error rightErrors =>
          simp [ResponseValueResultEquivalent] at hequivalent
      | ok rightResult =>
          rcases leftResult with ⟨leftValue, leftErrors⟩
          rcases rightResult with ⟨rightValue, rightErrors⟩
          exact
            ⟨responseValue_semanticEquivalent_object_cons hequivalent.1
                (responseValue_semanticEquivalent_refl (.object [])),
              hequivalent.2⟩

theorem executeField_singleton_equivalent_zero
    {ObjectRef : Type}
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues)
    (source : ResolverValue ObjectRef)
    (responseName executionParentType fieldName : Name)
    (leftArguments rightArguments : List Argument)
    (leftChild rightChild : List Selection)
    : SelectionSetResultEquivalent
        (executeField schema resolvers variableValues 0 source responseName
          [{
            parentType := executionParentType
            responseName := responseName
            fieldName := fieldName
            arguments := leftArguments
            selectionSet := leftChild
          }])
        (executeField schema resolvers variableValues 0 source responseName
          [{
            parentType := executionParentType
            responseName := responseName
            fieldName := fieldName
            arguments := rightArguments
            selectionSet := rightChild
          }]) := by
  simp [executeField, outOfFuel, SelectionSetResultEquivalent]

theorem executeField_singleton_equivalent_succ
    {fuel : Nat} (hcomplete : CompleteValueSoundAtFuel fuel)
    {ObjectRef : Type}
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues)
    (source : ResolverValue ObjectRef)
    (responseName executionParentType fieldName : Name)
    (leftArguments rightArguments : List Argument)
    (leftChild rightChild : List Selection)
    (normalChildParentType : Name)
    : Argument.argumentsEquivalent leftArguments rightArguments
      -> selectionSetDirectiveFree leftChild
      -> selectionSetDirectiveFree rightChild
      -> selectionSetNormal schema normalChildParentType leftChild
      -> selectionSetNormal schema normalChildParentType rightChild
      -> SelectionSetEqualUpToReordering leftChild rightChild
      -> SelectionSetResultEquivalent
          (executeField schema resolvers variableValues (fuel + 1) source
            responseName
            [{
              parentType := executionParentType
              responseName := responseName
              fieldName := fieldName
              arguments := leftArguments
              selectionSet := leftChild
            }])
          (executeField schema resolvers variableValues (fuel + 1) source
            responseName
            [{
              parentType := executionParentType
              responseName := responseName
              fieldName := fieldName
              arguments := rightArguments
              selectionSet := rightChild
            }]) := by
  intro harguments hleftFree hrightFree hleftNormal hrightNormal hequal
  cases hlookup : schema.lookupField executionParentType fieldName with
  | none =>
      simp [executeField, hlookup, SelectionSetResultEquivalent]
  | some fieldDefinition =>
      have hresolve :=
        resolvers.resolve_argumentsEquivalent executionParentType fieldName
          leftArguments rightArguments source harguments
      cases hleftResolve
            : resolvers.resolve executionParentType fieldName leftArguments source with
      | none =>
          have hrightResolve :
              resolvers.resolve executionParentType fieldName rightArguments
                source = none := by
            rw [← hresolve]
            exact hleftResolve
          simp only [executeField, hlookup, hleftResolve, hrightResolve]
          exact selectionSetResultEquivalent_of_eq rfl
      | some value =>
          have hrightResolve :
              resolvers.resolve executionParentType fieldName rightArguments
                source = some value := by
            rw [← hresolve]
            exact hleftResolve
          simp only [executeField, hlookup, hleftResolve, hrightResolve]
          apply selectionSetResultEquivalent_singleFieldResult
          exact hcomplete schema resolvers variableValues executionParentType
            responseName fieldName leftArguments rightArguments leftChild
            rightChild normalChildParentType fieldDefinition.outputType value
            harguments hleftFree hrightFree hleftNormal hrightNormal hequal

theorem singletonFieldSoundAtFuel_zero : SingletonFieldSoundAtFuel 0 := by
  intro ObjectRef schema resolvers variableValues source responseName
    executionParentType fieldName leftArguments rightArguments leftChild
    rightChild normalChildParentType _harguments _hleftFree _hrightFree
    _hleftNormal _hrightNormal _hequal
  exact executeField_singleton_equivalent_zero schema resolvers
    variableValues source responseName executionParentType fieldName
    leftArguments rightArguments leftChild rightChild

theorem singletonFieldSoundAtFuel_succ {fuel : Nat}
    : CompleteValueSoundAtFuel fuel -> SingletonFieldSoundAtFuel (fuel + 1) := by
  intro hcomplete ObjectRef schema resolvers variableValues source responseName
    executionParentType fieldName leftArguments rightArguments leftChild
    rightChild normalChildParentType harguments hleftFree hrightFree
    hleftNormal hrightNormal hequal
  exact executeField_singleton_equivalent_succ hcomplete schema resolvers
    variableValues source responseName executionParentType fieldName
    leftArguments rightArguments leftChild rightChild normalChildParentType
    harguments hleftFree hrightFree hleftNormal hrightNormal hequal

private theorem execute_paired_normal_field_groups_equivalent
    {fuel : Nat} (hfieldSound : SingletonFieldSoundAtFuel fuel)
    {ObjectRef : Type}
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues)
    (normalParentType executionParentType : Name)
    (source : ResolverValue ObjectRef)
    (left right : List Selection)
    (hleftFree : selectionSetDirectiveFree left)
    (hrightFree : selectionSetDirectiveFree right)
    (hleftNormal : selectionSetNormal schema normalParentType left)
    (hrightNormal : selectionSetNormal schema normalParentType right)
    (hobject : objectTypeNameBool schema normalParentType = true)
    : ∀ pairs : List (Selection × Selection),
        (∀ pair,
          pair ∈ pairs
          -> pair.1 ∈ left ∧ pair.2 ∈ right ∧ SelectionEqualUpToReordering pair.1 pair.2)
        -> SelectionSetResultEquivalent
            (executeCollectedFields schema resolvers variableValues fuel source
              (pairs.map (fun pair => fieldGroupOfSelection executionParentType pair.1)))
            (executeCollectedFields schema resolvers variableValues fuel source
              (pairs.map (fun pair => fieldGroupOfSelection executionParentType pair.2)))
  | [], _hpairs => selectionSetResultEquivalent_of_eq rfl
  | pair :: rest, hpairs => by
      rcases pair with ⟨leftSelection, rightSelection⟩
      rcases hpairs (leftSelection, rightSelection) (by simp) with
        ⟨hleftMem, hrightMem, hrelation⟩
      have hleftField : Selection.isField leftSelection :=
        (selectionSetNormal_allFields_of_object hleftNormal hobject)
          leftSelection hleftMem
      cases leftSelection with
      | inlineFragment typeCondition directives childSelectionSet =>
          simp [Selection.isField] at hleftField
      | field responseName fieldName leftArguments leftDirectives leftChild =>
          cases hrelation with
          | field _ _ _ harguments hchildren =>
              have hleftDirectives : leftDirectives = [] :=
                selectionSetDirectiveFree_field_directives_nil_of_mem
                  hleftFree hleftMem
              subst leftDirectives
              have hleftChildFree : selectionSetDirectiveFree leftChild :=
                selectionSetDirectiveFree_field_child_of_mem hleftFree hleftMem
              rename_i rightArguments rightChild
              have hrightChildFree : selectionSetDirectiveFree rightChild :=
                selectionSetDirectiveFree_field_child_of_mem hrightFree
                  hrightMem
              rcases selectionSetNormal_field_child_of_mem_with_returnType
                  hleftNormal hleftMem with
                ⟨returnType, hreturnType, hleftChildNormal⟩
              rcases selectionSetNormal_field_child_of_mem_with_returnType
                  hrightNormal hrightMem with
                ⟨rightReturnType, hrightReturnType, hrightChildNormal'⟩
              have hsameReturnType : rightReturnType = returnType := by
                rw [hreturnType] at hrightReturnType
                exact (Option.some.inj hrightReturnType).symm
              have hrightChildNormal :
                  selectionSetNormal schema returnType rightChild := by
                simpa [hsameReturnType] using hrightChildNormal'
              apply executeCollectedFields_cons_equivalent schema
                resolvers variableValues fuel source responseName _ _ _ _
              · exact hfieldSound schema resolvers variableValues source
                  responseName executionParentType fieldName leftArguments
                  rightArguments leftChild rightChild returnType harguments
                  hleftChildFree hrightChildFree hleftChildNormal
                  hrightChildNormal hchildren
              · exact execute_paired_normal_field_groups_equivalent
                  hfieldSound schema resolvers variableValues normalParentType
                  executionParentType source left right hleftFree hrightFree
                  hleftNormal hrightNormal hobject rest
                  (by
                    intro pair hpair
                    exact hpairs pair (List.mem_cons_of_mem _ hpair))

private theorem pairKeysNodup_of_executableGroupNamesNodup
    : ∀ groups : List (Name × List ExecutableField),
        executableGroupNamesNodup groups -> (groups.map Prod.fst).Nodup
  | [], _hnodup => by simp
  | group :: rest, hnodup => by
      apply List.nodup_cons.mpr
      exact
        ⟨hnodup.1,
          pairKeysNodup_of_executableGroupNamesNodup rest hnodup.2⟩

private theorem object_selectionSetSoundAtFuel_of_singletonFieldSound
    {fuel : Nat} (hfieldSound : SingletonFieldSoundAtFuel fuel)
    {ObjectRef : Type}
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues)
    (normalParentType executionParentType runtimeType : Name)
    (ref : ObjectRef) (left right : List Selection)
    : selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema normalParentType left
      -> selectionSetNormal schema normalParentType right
      -> SelectionSetEqualUpToReordering left right
      -> objectTypeNameBool schema normalParentType = true
      -> SelectionSetResultEquivalent
          (executeSelectionSet schema resolvers variableValues fuel
            executionParentType (.object runtimeType ref) left)
          (executeSelectionSet schema resolvers variableValues fuel
            executionParentType (.object runtimeType ref) right) := by
  intro hleftFree hrightFree hleftNormal hrightNormal hequal hobject
  have hleftAll : selectionsAllFields left :=
    selectionSetNormal_allFields_of_object hleftNormal hobject
  have hrightAll : selectionsAllFields right :=
    selectionSetNormal_allFields_of_object hrightNormal hobject
  have hleftCollect :
      collectFields schema variableValues executionParentType
        (.object runtimeType ref) left =
      left.map (fieldGroupOfSelection executionParentType) :=
    collectFields_allFields_directiveFree_nodup_eq_map schema variableValues
      executionParentType (.object runtimeType ref) left hleftAll hleftFree
      (selectionSetNormal_responseNamesNodup hleftNormal)
  have hrightCollect :
      collectFields schema variableValues executionParentType
        (.object runtimeType ref) right =
      right.map (fieldGroupOfSelection executionParentType) :=
    collectFields_allFields_directiveFree_nodup_eq_map schema variableValues
      executionParentType (.object runtimeType ref) right hrightAll hrightFree
      (selectionSetNormal_responseNamesNodup hrightNormal)
  rcases hequal with ⟨pairs, hleftPerm, hrightPerm, hrelations⟩
  let leftPairGroups :=
    pairs.map
      (fun pair => fieldGroupOfSelection executionParentType pair.1)
  let rightPairGroups :=
    pairs.map
      (fun pair => fieldGroupOfSelection executionParentType pair.2)
  have hleftGroupPerm :
      leftPairGroups.Perm
        (left.map (fieldGroupOfSelection executionParentType)) := by
    simpa [leftPairGroups, List.map_map, Function.comp_def] using
      hleftPerm.map (fieldGroupOfSelection executionParentType)
  have hrightGroupPerm :
      rightPairGroups.Perm
        (right.map (fieldGroupOfSelection executionParentType)) := by
    simpa [rightPairGroups, List.map_map, Function.comp_def] using
      hrightPerm.map (fieldGroupOfSelection executionParentType)
  have hleftCollectNodup :
      ((left.map (fieldGroupOfSelection executionParentType)).map
        Prod.fst).Nodup := by
    rw [← hleftCollect]
    exact pairKeysNodup_of_executableGroupNamesNodup _
      (collectFields_namesNodup schema variableValues executionParentType
        (.object runtimeType ref) left)
  have hrightCollectNodup :
      ((right.map (fieldGroupOfSelection executionParentType)).map
        Prod.fst).Nodup := by
    rw [← hrightCollect]
    exact pairKeysNodup_of_executableGroupNamesNodup _
      (collectFields_namesNodup schema variableValues executionParentType
        (.object runtimeType ref) right)
  have hpairsEquivalent :
      SelectionSetResultEquivalent
        (executeCollectedFields schema resolvers variableValues fuel
          (.object runtimeType ref) leftPairGroups)
        (executeCollectedFields schema resolvers variableValues fuel
          (.object runtimeType ref) rightPairGroups) := by
    apply execute_paired_normal_field_groups_equivalent hfieldSound schema
      resolvers variableValues normalParentType executionParentType
      (.object runtimeType ref) left right hleftFree hrightFree hleftNormal
      hrightNormal hobject pairs
    intro pair hpair
    have hleftPairMem : pair.1 ∈ pairs.map Prod.fst :=
      List.mem_map.mpr ⟨pair, hpair, rfl⟩
    have hrightPairMem : pair.2 ∈ pairs.map Prod.snd :=
      List.mem_map.mpr ⟨pair, hpair, rfl⟩
    exact
      ⟨hleftPerm.mem_iff.mp hleftPairMem,
        hrightPerm.mem_iff.mp hrightPairMem,
        hrelations pair hpair⟩
  have hleftReorder :
      SelectionSetResultEquivalent
        (executeCollectedFields schema resolvers variableValues fuel
          (.object runtimeType ref)
          (left.map (fieldGroupOfSelection executionParentType)))
        (executeCollectedFields schema resolvers variableValues fuel
          (.object runtimeType ref) leftPairGroups) :=
    executeCollectedFields_equivalent_of_perm schema resolvers
      variableValues fuel (.object runtimeType ref) hleftGroupPerm.symm
      hleftCollectNodup
  have hrightReorder :
      SelectionSetResultEquivalent
        (executeCollectedFields schema resolvers variableValues fuel
          (.object runtimeType ref) rightPairGroups)
        (executeCollectedFields schema resolvers variableValues fuel
          (.object runtimeType ref)
          (right.map (fieldGroupOfSelection executionParentType))) :=
    executeCollectedFields_equivalent_of_perm schema resolvers
      variableValues fuel (.object runtimeType ref) hrightGroupPerm
      ((hrightGroupPerm.map Prod.fst).nodup_iff.mpr hrightCollectNodup)
  simpa [executeSelectionSet, executeRootSelectionSet, hleftCollect,
    hrightCollect] using
    selectionSetResultEquivalent_trans hleftReorder
      (selectionSetResultEquivalent_trans hpairsEquivalent hrightReorder)

private theorem executeSelectionSet_singleton_runtimeFragment_eq_child
    {ObjectRef : Type}
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (fuel : Nat)
    (executionParentType runtimeType : Name) (ref : ObjectRef)
    (childSelectionSet : List Selection)
    : objectTypeNameBool schema runtimeType = true
      -> executeSelectionSet schema resolvers variableValues fuel
            executionParentType (.object runtimeType ref)
            [Selection.inlineFragment (some runtimeType) [] childSelectionSet]
          = executeSelectionSet schema resolvers variableValues fuel
              executionParentType (.object runtimeType ref) childSelectionSet := by
  intro hruntimeObject
  have happly :
      doesFragmentTypeApplyBool schema executionParentType
        (.object runtimeType ref) runtimeType = true := by
    simp [doesFragmentTypeApplyBool, runtimeObjectType?,
      typeIncludesObjectBool_self_of_objectTypeNameBool schema hruntimeObject]
  simp [executeSelectionSet, executeRootSelectionSet, collectFields,
    collectSelection, ExecutionKeys.selectionDirectivesAllowBool_nil,
    happly, mergeExecutableGroups]

theorem selectionSetSoundAtFuel_of_singletonFieldSound {fuel : Nat}
    : SingletonFieldSoundAtFuel fuel -> SelectionSetSoundAtFuel fuel := by
  intro hfieldSound ObjectRef schema resolvers variableValues normalParentType
    executionParentType runtimeType ref left right hleftFree hrightFree
    hleftNormal hrightNormal hequal hexecutionScope
  by_cases hobject : objectTypeNameBool schema normalParentType = true
  · exact object_selectionSetSoundAtFuel_of_singletonFieldSound hfieldSound
      schema resolvers variableValues normalParentType executionParentType
      runtimeType ref left right hleftFree hrightFree hleftNormal hrightNormal
      hequal hobject
  · have hnonObject :
        objectTypeNameBool schema normalParentType = false := by
      cases hvalue : objectTypeNameBool schema normalParentType
      · rfl
      · exact False.elim (hobject hvalue)
    have hrightConditionIff :=
      inlineFragmentTypeCondition_mem_iff_of_equalUpToReordering
        (typeCondition := runtimeType) hequal
    by_cases hruntimeMem :
        runtimeType ∈ left.filterMap inlineFragmentTypeCondition?
    · rcases List.mem_filterMap.mp hruntimeMem with
        ⟨leftSelection, hleftMem, hleftCondition⟩
      cases leftSelection with
      | field responseName fieldName arguments directives childSelectionSet =>
          simp [inlineFragmentTypeCondition?] at hleftCondition
      | inlineFragment maybeTypeCondition leftDirectives leftBody =>
          cases maybeTypeCondition with
          | none =>
              simp [inlineFragmentTypeCondition?] at hleftCondition
          | some matchedTypeCondition =>
              simp [inlineFragmentTypeCondition?] at hleftCondition
              subst matchedTypeCondition
              have hleftDirectives : leftDirectives = [] :=
                selectionSetDirectiveFree_inlineFragment_directives_nil_of_mem
                  hleftFree hleftMem
              subst leftDirectives
              rcases selectionSetEqualUpToReordering_left_mem hequal
                  hleftMem with
                ⟨rightSelection, hrightMem, hrelation⟩
              cases hrelation with
              | inlineFragment _ _ hchildren =>
                  rename_i rightBody
                  rcases selectionSetNormal_inlineFragment_child_of_mem
                      hleftNormal hleftMem with
                    ⟨hruntimeObjectProp, hleftBodyNormal⟩
                  rcases selectionSetNormal_inlineFragment_child_of_mem
                      hrightNormal hrightMem with
                    ⟨_hrightRuntimeObjectProp, hrightBodyNormal⟩
                  have hruntimeObject :
                      objectTypeNameBool schema runtimeType = true :=
                    objectTypeNameBool_eq_true_of_objectType_forNormality
                      schema hruntimeObjectProp
                  have hleftBodyFree :
                      selectionSetDirectiveFree leftBody :=
                    selectionSetDirectiveFree_inlineFragment_child_of_mem
                      hleftFree hleftMem
                  have hrightBodyFree :
                      selectionSetDirectiveFree rightBody :=
                    selectionSetDirectiveFree_inlineFragment_child_of_mem
                      hrightFree hrightMem
                  rcases List.mem_iff_append.mp hleftMem with
                    ⟨leftPref, leftSuffix, hleftSelectionSet⟩
                  rcases List.mem_iff_append.mp hrightMem with
                    ⟨rightPref, rightSuffix, hrightSelectionSet⟩
                  have hexecutionParent :
                      executionParentType = normalParentType
                        ∨ executionParentType = runtimeType := by
                    rcases hexecutionScope with hnormalObject
                      | hnormalExecution | hruntimeExecution
                    · exact False.elim (hobject hnormalObject)
                    · exact Or.inl hnormalExecution
                    · exact Or.inr hruntimeExecution
                  have hleftMiddle :
                      executeSelectionSet schema resolvers variableValues fuel
                        executionParentType (.object runtimeType ref) left =
                      executeSelectionSet schema resolvers variableValues fuel
                        executionParentType (.object runtimeType ref)
                        [Selection.inlineFragment (some runtimeType) []
                          leftBody] := by
                    rcases hexecutionParent with hnormalExecution
                      | hruntimeExecution
                    · subst executionParentType
                      simpa [hleftSelectionSet] using
                        executeSelectionSet_middle_inlineFragment_only_eq_singleton_at_object_runtime_source
                          schema resolvers variableValues fuel ref
                          (pref := leftPref) (childSelectionSet := leftBody)
                          (suffix := leftSuffix) hnonObject hruntimeObject
                          (hleftSelectionSet ▸ hleftFree)
                          (hleftSelectionSet ▸ hleftNormal)
                    · subst executionParentType
                      simpa [hleftSelectionSet] using
                        executeSelectionSet_middle_inlineFragment_only_eq_singleton_at_runtime_parent
                          schema resolvers variableValues fuel ref
                          (pref := leftPref) (childSelectionSet := leftBody)
                          (suffix := leftSuffix) hnonObject hruntimeObject
                          (hleftSelectionSet ▸ hleftFree)
                          (hleftSelectionSet ▸ hleftNormal)
                  have hrightMiddle :
                      executeSelectionSet schema resolvers variableValues fuel
                        executionParentType (.object runtimeType ref) right =
                      executeSelectionSet schema resolvers variableValues fuel
                        executionParentType (.object runtimeType ref)
                        [Selection.inlineFragment (some runtimeType) []
                          rightBody] := by
                    rcases hexecutionParent with hnormalExecution
                      | hruntimeExecution
                    · subst executionParentType
                      simpa [hrightSelectionSet] using
                        executeSelectionSet_middle_inlineFragment_only_eq_singleton_at_object_runtime_source
                          schema resolvers variableValues fuel ref
                          (pref := rightPref) (childSelectionSet := rightBody)
                          (suffix := rightSuffix) hnonObject hruntimeObject
                          (hrightSelectionSet ▸ hrightFree)
                          (hrightSelectionSet ▸ hrightNormal)
                    · subst executionParentType
                      simpa [hrightSelectionSet] using
                        executeSelectionSet_middle_inlineFragment_only_eq_singleton_at_runtime_parent
                          schema resolvers variableValues fuel ref
                          (pref := rightPref) (childSelectionSet := rightBody)
                          (suffix := rightSuffix) hnonObject hruntimeObject
                          (hrightSelectionSet ▸ hrightFree)
                          (hrightSelectionSet ▸ hrightNormal)
                  have hleftSingleton :
                      executeSelectionSet schema resolvers variableValues fuel
                        executionParentType (.object runtimeType ref)
                        [Selection.inlineFragment (some runtimeType) []
                          leftBody] =
                      executeSelectionSet schema resolvers variableValues fuel
                        executionParentType (.object runtimeType ref)
                        leftBody :=
                    executeSelectionSet_singleton_runtimeFragment_eq_child
                      schema resolvers variableValues fuel executionParentType
                      runtimeType ref leftBody hruntimeObject
                  have hrightSingleton :
                      executeSelectionSet schema resolvers variableValues fuel
                        executionParentType (.object runtimeType ref)
                        [Selection.inlineFragment (some runtimeType) []
                          rightBody] =
                      executeSelectionSet schema resolvers variableValues fuel
                        executionParentType (.object runtimeType ref)
                        rightBody :=
                    executeSelectionSet_singleton_runtimeFragment_eq_child
                      schema resolvers variableValues fuel executionParentType
                      runtimeType ref rightBody hruntimeObject
                  have hbodyEquivalent :=
                    object_selectionSetSoundAtFuel_of_singletonFieldSound
                      hfieldSound schema resolvers variableValues runtimeType
                      executionParentType runtimeType ref leftBody rightBody
                      hleftBodyFree hrightBodyFree hleftBodyNormal
                      hrightBodyNormal hchildren hruntimeObject
                  rw [hleftMiddle, hrightMiddle, hleftSingleton,
                    hrightSingleton]
                  exact hbodyEquivalent
    · have hrightRuntimeNotMem :
          runtimeType ∉ right.filterMap inlineFragmentTypeCondition? := by
        intro hrightMem
        exact hruntimeMem (hrightConditionIff.mpr hrightMem)
      have hleftCollect :
          collectFields schema variableValues executionParentType
            (.object runtimeType ref) left = [] :=
        collectFields_inlineFragments_without_typeCondition_eq_nil_at_runtime_parent
          schema variableValues ref hnonObject hleftFree hleftNormal hruntimeMem
      have hrightCollect :
          collectFields schema variableValues executionParentType
            (.object runtimeType ref) right = [] :=
        collectFields_inlineFragments_without_typeCondition_eq_nil_at_runtime_parent
          schema variableValues ref hnonObject hrightFree hrightNormal
          hrightRuntimeNotMem
      simp [executeSelectionSet, executeRootSelectionSet, hleftCollect,
        hrightCollect, executeCollectedFields, SelectionSetResultEquivalent,
        responseValue_semanticEquivalent_refl]

theorem completeValueSoundAtFuel_zero : CompleteValueSoundAtFuel 0 := by
  intro ObjectRef schema resolvers variableValues executionParentType
    responseName fieldName leftArguments rightArguments leftChild rightChild
    normalChildParentType fieldType value _harguments _hleftFree _hrightFree
    _hleftNormal _hrightNormal _hequal
  simp [completeValue, outOfFuel, ResponseValueResultEquivalent]

theorem completeValueSoundAtFuel_succ {fuel : Nat}
    : SelectionSetSoundAtFuel fuel
      -> CompleteValueSoundAtFuel fuel
      -> CompleteValueSoundAtFuel (fuel + 1) := by
  intro hselection hcomplete ObjectRef schema resolvers variableValues
    executionParentType responseName fieldName leftArguments rightArguments
    leftChild rightChild normalChildParentType fieldType value harguments
    hleftFree hrightFree hleftNormal hrightNormal hequal
  induction fieldType generalizing value with
  | nonNull inner ih =>
      simp only [completeValue]
      apply responseValueResultEquivalent_nonNullCompletion
      exact ih value
  | named typeName =>
      cases value with
      | null =>
          simp only [completeValue, ResponseValueResultEquivalent]
          exact ⟨responseValue_semanticEquivalent_refl .null, trivial⟩
      | scalar scalarValue =>
          cases hcomposite : (TypeRef.named typeName).isCompositeBool schema <;>
            simp [completeValue, hcomposite,
              ResponseValueResultEquivalent,
              ResponseValue.semanticEquivalent, ResponseValue.canonical]
      | list values =>
          simp [completeValue, ResponseValueResultEquivalent]
      | object runtimeType ref =>
          by_cases hincludes :
              schema.typeIncludesObjectBool typeName runtimeType = true
          · have hscope :
                objectTypeNameBool schema normalChildParentType = true
                  ∨ runtimeType = normalChildParentType
                  ∨ runtimeType = runtimeType := by
              by_cases hchildObject :
                  objectTypeNameBool schema normalChildParentType = true
              · exact Or.inl hchildObject
              · exact Or.inr (Or.inr rfl)
            have hchildEquivalent :=
              hselection schema resolvers variableValues normalChildParentType
                runtimeType runtimeType ref leftChild rightChild hleftFree
                hrightFree hleftNormal hrightNormal hequal hscope
            simp only [completeValue, hincludes, if_true]
            apply selectionSetResultEquivalent_catchBubbleAsNull
            simpa [executeSelectionSet, executeRootSelectionSet,
              collectSubfields, mergeExecutableGroups] using hchildEquivalent
          · have hincludesFalse :
                schema.typeIncludesObjectBool typeName runtimeType = false := by
              cases hvalue :
                  schema.typeIncludesObjectBool typeName runtimeType
              · rfl
              · exact False.elim (hincludes hvalue)
            simp [completeValue, hincludesFalse,
              ResponseValueResultEquivalent]
  | list inner =>
      cases value with
      | null =>
          simp only [completeValue, ResponseValueResultEquivalent]
          exact ⟨responseValue_semanticEquivalent_refl .null, trivial⟩
      | scalar scalarValue =>
          simp [completeValue, ResponseValueResultEquivalent]
      | object runtimeType ref =>
          simp [completeValue, ResponseValueResultEquivalent]
      | list values =>
          have hvalues :
              ListResponseValueResultEquivalent
                (completeValueList schema resolvers variableValues fuel inner
                  [{
                    parentType := executionParentType
                    responseName := responseName
                    fieldName := fieldName
                    arguments := leftArguments
                    selectionSet := leftChild
                  }] values)
                (completeValueList schema resolvers variableValues fuel inner
                  [{
                    parentType := executionParentType
                    responseName := responseName
                    fieldName := fieldName
                    arguments := rightArguments
                    selectionSet := rightChild
                  }] values) := by
            induction values with
            | nil =>
                simp [completeValueList,
                  ListResponseValueResultEquivalent]
            | cons value rest ih =>
                simp only [completeValueList]
                apply listResponseValueResultEquivalent_combine_cons
                · exact hcomplete schema resolvers variableValues
                    executionParentType responseName fieldName leftArguments
                    rightArguments leftChild rightChild normalChildParentType
                    inner value harguments hleftFree hrightFree hleftNormal
                    hrightNormal hequal
                · exact ih
          simp only [completeValue]
          exact listResponseValueResultEquivalent_catchBubbleAsNull hvalues

theorem selectionSetSound_completeValueSound_atFuel
    : ∀ fuel : Nat, SelectionSetSoundAtFuel fuel ∧ CompleteValueSoundAtFuel fuel
  | 0 =>
      ⟨selectionSetSoundAtFuel_of_singletonFieldSound
          singletonFieldSoundAtFuel_zero,
        completeValueSoundAtFuel_zero⟩
  | fuel + 1 => by
      rcases selectionSetSound_completeValueSound_atFuel fuel with
        ⟨hselection, hcomplete⟩
      have hfield : SingletonFieldSoundAtFuel (fuel + 1) :=
        singletonFieldSoundAtFuel_succ hcomplete
      exact
        ⟨selectionSetSoundAtFuel_of_singletonFieldSound hfield,
          completeValueSoundAtFuel_succ hselection hcomplete⟩

theorem responseEquivalent_of_selectionSetResultEquivalent
    {left right : Result (List (Name × ResponseValue))}
    : SelectionSetResultEquivalent left right
      -> Response.semanticEquivalent
          (Execution.selectionSetResultToResponse left)
          (Execution.selectionSetResultToResponse right) := by
  intro hequivalent
  cases left <;> cases right <;>
    simp [SelectionSetResultEquivalent, Execution.selectionSetResultToResponse,
      Response.semanticEquivalent, ResponseValue.semanticEquivalent,
      ResponseValue.canonical] at hequivalent ⊢
  all_goals exact hequivalent

theorem normal_selectionSetsSemanticallyEquivalent_of_equalUpToReordering
    {schema : Schema} {parentType : Name} {left right : List Selection}
    : selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> SelectionSetEqualUpToReordering left right
      -> selectionSetsSemanticallyEquivalent schema parentType left right := by
  intro hleftFree hrightFree hleftNormal hrightNormal hequal ObjectRef
    resolvers variableValues fuel source hsource
  rcases hsource with ⟨runtimeType, ref, hsource, _hincludes⟩
  subst source
  have hresultEquivalent :=
    (selectionSetSound_completeValueSound_atFuel fuel).1 schema resolvers
      variableValues parentType parentType runtimeType ref left right
      hleftFree hrightFree hleftNormal hrightNormal hequal
      (Or.inr (Or.inl rfl))
  exact responseEquivalent_of_selectionSetResultEquivalent
    hresultEquivalent

end ReorderingSoundness

theorem selectionSetsSemanticallyEquivalent_of_equalUpToReordering
    {schema : Schema} {parentType : Name} {left right : List Selection}
    : normalSelectionSetsEqualUpToReorderingSemanticallyEquivalent
        schema parentType left right :=
  ReorderingSoundness.normal_selectionSetsSemanticallyEquivalent_of_equalUpToReordering

theorem selectionSetsDataEquivalent_of_equalUpToReordering
    {schema : Schema} {parentType : Name} {left right : List Selection}
    : selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> SelectionSetEqualUpToReordering left right
      -> selectionSetsDataEquivalent schema parentType left right := by
  intro hleftFree hrightFree hleftNormal hrightNormal hequal
  exact selectionSetsDataEquivalent_of_selectionSetsSemanticallyEquivalent
    (selectionSetsSemanticallyEquivalent_of_equalUpToReordering
      hleftFree hrightFree hleftNormal hrightNormal hequal)

end GroundTypeNormalization

end NormalForm

end GraphQL
