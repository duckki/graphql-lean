import Proofs.GraphQL.Theories.TreeSummary.ExactCases.BooleanDecision
import Proofs.GraphQL.Theories.TreeSummary.ExactCases.ResolvedContext

/-! Refinement from one concrete Boolean environment to the unknown-variable summary. -/

namespace GraphQL
namespace TreeSummary
namespace ExactCases

open GraphQL.Execution
open GraphQL.ConditionTree
open Internal

namespace Internal.BooleanDecision

def selectedValue (variableValues : VariableValues) (variableName : Name) : Bool :=
  (inputValueBoolean? variableValues (.variable variableName)).getD false

-- Chooses the request's branch at Boolean tests while retaining factored type joins.
def select (variableValues : VariableValues) : BooleanDecision α -> BooleanDecision α
  | .leaf summary => .leaf summary
  | .split test onFalse onTrue =>
      if selectedValue variableValues test then
        select variableValues onTrue
      else
        select variableValues onFalse
  | .join left right =>
      .join (select variableValues left) (select variableValues right)

theorem select_map (variableValues : VariableValues) (transform : α -> β)
    (decision : BooleanDecision α)
    : select variableValues (decision.map transform)
      = (select variableValues decision).map transform := by
  induction decision with
  | leaf => rfl
  | split test onFalse onTrue ihFalse ihTrue =>
      simp only [map, select]
      split <;> assumption
  | join left right ihLeft ihRight =>
      simp [map, select, ihLeft, ihRight]

theorem select_restrict (variableValues : VariableValues)
    (selectedVariable : Name) (selected : Bool)
    (hselected : selectedValue variableValues selectedVariable = selected)
    (decision : BooleanDecision α)
    : select variableValues (decision.restrict selectedVariable selected)
      = select variableValues decision := by
  induction decision with
  | leaf => rfl
  | split test onFalse onTrue ihFalse ihTrue =>
      simp only [restrict, select]
      by_cases heq : test = selectedVariable
      · subst test
        simp only [hselected]
        cases selected <;> simp [ihFalse, ihTrue]
      · simp only [if_neg heq]
        simp [select, ihFalse, ihTrue]
  | join left right ihLeft ihRight =>
      simp [restrict, select, ihLeft, ihRight]

def leaves : BooleanDecision α -> List α
  | .leaf value => [value]
  | .split _test onFalse onTrue => leaves onFalse ++ leaves onTrue
  | .join left right => leaves left ++ leaves right

def SplitFree : BooleanDecision α -> Prop
  | .leaf _value => True
  | .split _test _onFalse _onTrue => False
  | .join left right => left.SplitFree ∧ right.SplitFree

theorem select_splitFree (variableValues : VariableValues) (decision : BooleanDecision α)
    : (select variableValues decision).SplitFree := by
  induction decision with
  | leaf => trivial
  | split test onFalse onTrue ihFalse ihTrue =>
      simp only [select]
      split <;> assumption
  | join left right ihLeft ihRight => exact ⟨ihLeft, ihRight⟩

theorem select_eq_self_of_splitFree (variableValues : VariableValues)
    {decision : BooleanDecision α} (hfree : decision.SplitFree)
    : select variableValues decision = decision := by
  induction decision with
  | leaf => rfl
  | split => contradiction
  | join left right ihLeft ihRight =>
      simp [select, ihLeft hfree.1, ihRight hfree.2]

theorem mem_leaves_map {value : β} (transform : α -> β) (decision : BooleanDecision α)
    : value ∈ (decision.map transform).leaves
      ↔ ∃ source, source ∈ decision.leaves ∧ value = transform source := by
  induction decision with
  | leaf source => simp [map, leaves]
  | split test onFalse onTrue ihFalse ihTrue =>
      simp only [map, leaves, List.mem_append, ihFalse, ihTrue]
      grind
  | join left right ihLeft ihRight =>
      simp only [map, leaves, List.mem_append, ihLeft, ihRight]
      grind

theorem mem_leaves_select_zipWith (variableValues : VariableValues)
    (variableOrder : BooleanVariableNames) (operation : α -> β -> γ)
    (left : BooleanDecision α) (right : BooleanDecision β) (value : γ)
    : value ∈ (select variableValues (zipWith variableOrder operation left right)).leaves
      ↔ ∃ leftValue,
          leftValue ∈ (select variableValues left).leaves
          ∧ ∃ rightValue,
              rightValue ∈ (select variableValues right).leaves
              ∧ value = operation leftValue rightValue := by
  induction left, right using BooleanDecision.zipWith.induct variableOrder with
  | case1 left right =>
      simp [zipWith, select, select_map, leaves, mem_leaves_map]
  | case2 left right hnotLeaf =>
      cases left <;>
        simp_all [zipWith, select, select_map, leaves, mem_leaves_map]
  | case3 leftFirst leftSecond right hnotLeaf ihFirst ihSecond =>
      cases right <;> simp_all [zipWith, select, leaves] <;>
        grind
  | case4 left rightFirst rightSecond hnotLeaf hnotJoin ihFirst ihSecond =>
      cases left <;> simp_all [zipWith, select, leaves] <;>
        grind
  | case5 leftFalse leftTrue test rightFalse rightTrue ihFalse ihTrue =>
      by_cases hselected : selectedValue variableValues test
      · simpa [zipWith, select, leaves, hselected] using ihTrue
      · simpa [zipWith, select, leaves, hselected] using ihFalse
  | case6 leftTest leftFalse leftTrue rightTest rightFalse rightTrue
      hne horder ihFalse ihTrue =>
      by_cases hselected : selectedValue variableValues leftTest
      · simp only [zipWith, if_neg hne, if_pos horder]
        simp only [select, hselected, if_true]
        rw [ihTrue]
        rw [select_restrict variableValues leftTest true (by simp [hselected])]
        simp [select]
      · have hselectedFalse : selectedValue variableValues leftTest = false :=
          by cases hvalue : selectedValue variableValues leftTest <;> simp_all
        simp only [zipWith, if_neg hne, if_pos horder]
        simp only [select, hselectedFalse, Bool.false_eq_true, if_false]
        rw [ihFalse]
        rw [select_restrict variableValues leftTest false (by simp [hselected])]
        simp [select]
  | case7 leftTest leftFalse leftTrue rightTest rightFalse rightTrue
      hne horder ihFalse ihTrue =>
      by_cases hselected : selectedValue variableValues rightTest
      · simp only [zipWith, if_neg hne, if_neg horder]
        simp only [select, hselected, if_true]
        rw [ihTrue]
        rw [select_restrict variableValues rightTest true (by simp [hselected])]
        simp [select]
      · have hselectedFalse : selectedValue variableValues rightTest = false :=
          by cases hvalue : selectedValue variableValues rightTest <;> simp_all
        simp only [zipWith, if_neg hne, if_neg horder]
        simp only [select, hselectedFalse, Bool.false_eq_true, if_false]
        rw [ihFalse]
        rw [select_restrict variableValues rightTest false (by simp [hselected])]
        simp [select]

theorem map_splitFree (transform : α -> β) {decision : BooleanDecision α}
    (hfree : decision.SplitFree)
    : (decision.map transform).SplitFree := by
  induction decision with
  | leaf => trivial
  | split => contradiction
  | join left right ihLeft ihRight => exact ⟨ihLeft hfree.1, ihRight hfree.2⟩

theorem zipWith_splitFree (variableOrder : BooleanVariableNames)
    (operation : α -> β -> γ) {left : BooleanDecision α}
    {right : BooleanDecision β} (hleft : left.SplitFree) (hright : right.SplitFree)
    : (zipWith variableOrder operation left right).SplitFree := by
  induction left generalizing right with
  | leaf left =>
      rw [zipWith]
      exact map_splitFree _ hright
  | split => contradiction
  | join leftFirst leftSecond ihFirst ihSecond =>
      cases right with
      | leaf right =>
          simpa [zipWith] using map_splitFree (fun value => operation value right) hleft
      | split rightTest rightFalse rightTrue => contradiction
      | join rightFirst rightSecond =>
          simpa [zipWith, SplitFree] using
            And.intro (ihFirst hleft.1 hright) (ihSecond hleft.2 hright)

theorem zipWith_eq_of_splitFree (leftOrder rightOrder : BooleanVariableNames)
    (operation : α -> β -> γ) {left : BooleanDecision α}
    {right : BooleanDecision β} (hleft : left.SplitFree) (hright : right.SplitFree)
    : zipWith leftOrder operation left right
      = zipWith rightOrder operation left right := by
  induction left generalizing right with
  | leaf => simp [zipWith]
  | split => contradiction
  | join leftFirst leftSecond ihFirst ihSecond =>
      cases right with
      | leaf => simp [zipWith]
      | split => contradiction
      | join rightFirst rightSecond =>
          simp only [zipWith]
          rw [ihFirst hleft.1 hright, ihSecond hleft.2 hright]

theorem mem_leaves_zipWith_of_splitFree
    (variableValues : VariableValues) (variableOrder : BooleanVariableNames)
    (operation : α -> β -> γ) {left : BooleanDecision α}
    {right : BooleanDecision β} (hleft : left.SplitFree) (hright : right.SplitFree)
    (value : γ)
    : value ∈ (zipWith variableOrder operation left right).leaves
      ↔ ∃ leftValue,
          leftValue ∈ left.leaves
          ∧ ∃ rightValue,
              rightValue ∈ right.leaves ∧ value = operation leftValue rightValue := by
  have hzip := mem_leaves_select_zipWith variableValues variableOrder operation
    left right value
  rw [select_eq_self_of_splitFree variableValues hleft,
    select_eq_self_of_splitFree variableValues hright] at hzip
  rw [select_eq_self_of_splitFree variableValues
    (zipWith_splitFree variableOrder operation hleft hright)] at hzip
  exact hzip

structure Refines (variableValues : VariableValues)
    (resolved symbolic : BooleanDecision α)
    : Prop where
  splitFree : resolved.SplitFree
  leaves
    : ∀ value, value ∈ resolved.leaves -> value ∈ (select variableValues symbolic).leaves

theorem Refines.leaf (variableValues : VariableValues) (value : α)
    : Refines variableValues (.leaf value) (.leaf value) := by
  exact ⟨True.intro, by simp [select]⟩

theorem Refines.map (variableValues : VariableValues) (transform : α -> β)
    {resolved symbolic : BooleanDecision α}
    (hrefines : Refines variableValues resolved symbolic)
    : Refines variableValues (resolved.map transform) (symbolic.map transform) := by
  constructor
  · exact map_splitFree transform hrefines.splitFree
  · intro value hvalue
    rw [mem_leaves_map] at hvalue
    rcases hvalue with ⟨source, hsource, rfl⟩
    rw [select_map, mem_leaves_map]
    exact ⟨source, hrefines.leaves source hsource, rfl⟩

theorem Refines.join (variableValues : VariableValues)
    {resolvedLeft resolvedRight symbolicLeft symbolicRight : BooleanDecision α}
    (hleft : Refines variableValues resolvedLeft symbolicLeft)
    (hright : Refines variableValues resolvedRight symbolicRight)
    : Refines variableValues (.join resolvedLeft resolvedRight)
        (.join symbolicLeft symbolicRight) := by
  constructor
  · exact ⟨hleft.splitFree, hright.splitFree⟩
  · intro value hvalue
    change value ∈ resolvedLeft.leaves ++ resolvedRight.leaves at hvalue
    rw [List.mem_append] at hvalue
    change value ∈
      (select variableValues symbolicLeft).leaves ++
        (select variableValues symbolicRight).leaves
    rw [List.mem_append]
    rcases hvalue with hvalue | hvalue
    · exact Or.inl (hleft.leaves value hvalue)
    · exact Or.inr (hright.leaves value hvalue)

theorem Refines.of_select_eq (variableValues : VariableValues)
    {resolved selected symbolic : BooleanDecision α}
    (hselect : select variableValues symbolic = select variableValues selected)
    (hrefines : Refines variableValues resolved selected)
    : Refines variableValues resolved symbolic := by
  exact ⟨hrefines.splitFree, fun value hvalue => hselect.symm ▸
    hrefines.leaves value hvalue⟩

theorem Refines.zipWith (variableValues : VariableValues)
    (variableOrder : BooleanVariableNames) (operation : α -> β -> γ)
    {resolvedLeft symbolicLeft : BooleanDecision α}
    {resolvedRight symbolicRight : BooleanDecision β}
    (hleft : Refines variableValues resolvedLeft symbolicLeft)
    (hright : Refines variableValues resolvedRight symbolicRight)
    : Refines variableValues
        (BooleanDecision.zipWith variableOrder operation resolvedLeft resolvedRight)
        (BooleanDecision.zipWith variableOrder operation symbolicLeft symbolicRight) := by
  constructor
  · exact zipWith_splitFree variableOrder operation hleft.splitFree hright.splitFree
  · intro value hvalue
    rw [mem_leaves_zipWith_of_splitFree variableValues variableOrder operation
      hleft.splitFree hright.splitFree] at hvalue
    rcases hvalue with
      ⟨leftValue, hleftValue, rightValue, hrightValue, rfl⟩
    rw [mem_leaves_select_zipWith]
    exact ⟨leftValue, hleft.leaves leftValue hleftValue,
      rightValue, hright.leaves rightValue hrightValue, rfl⟩

theorem Refines.combineMap (algebra : Algebra) (variableValues : VariableValues)
    (variableOrder : BooleanVariableNames) (items : List α)
    (resolved symbolic : ∀ item, item ∈ items -> BooleanDecision algebra.Summary)
    (hrefines
      : ∀ item hitem, Refines variableValues (resolved item hitem) (symbolic item hitem))
    : Refines variableValues
        (BooleanDecision.combineMap algebra variableOrder items resolved)
        (BooleanDecision.combineMap algebra variableOrder items symbolic) := by
  induction items with
  | nil => simpa [BooleanDecision.combineMap] using
      Refines.leaf variableValues algebra.empty
  | cons item rest ih =>
      rw [BooleanDecision.combineMap, BooleanDecision.combineMap]
      apply Refines.zipWith variableValues variableOrder algebra.combine
      · exact hrefines item (by simp)
      · exact ih
          (fun candidate hcandidate => resolved candidate (by simp [hcandidate]))
          (fun candidate hcandidate => symbolic candidate (by simp [hcandidate]))
          (fun candidate hcandidate => hrefines candidate (by simp [hcandidate]))

theorem Refines.joinMap (algebra : Algebra) (variableValues : VariableValues)
    (items : List α)
    (resolved symbolic : ∀ item, item ∈ items -> BooleanDecision algebra.Summary)
    (hrefines
      : ∀ item hitem, Refines variableValues (resolved item hitem) (symbolic item hitem))
    : Refines variableValues
        (BooleanDecision.joinMap algebra items resolved)
        (BooleanDecision.joinMap algebra items symbolic) := by
  cases items with
  | nil => simpa [BooleanDecision.joinMap] using
      Refines.leaf variableValues algebra.empty
  | cons item rest =>
      cases rest with
      | nil => simpa [BooleanDecision.joinMap] using hrefines item (by simp)
      | cons next tail =>
          rw [BooleanDecision.joinMap, BooleanDecision.joinMap]
          exact Refines.join variableValues (hrefines item (by simp))
            (Refines.joinMap algebra variableValues (next :: tail)
              (fun candidate hcandidate => resolved candidate (by simp [hcandidate]))
              (fun candidate hcandidate => symbolic candidate (by simp [hcandidate]))
              (fun candidate hcandidate => hrefines candidate (by simp [hcandidate])))

theorem le_collapse_of_mem (algebra : Algebra) (lawful : algebra.Lawful)
    (decision : BooleanDecision algebra.Summary) (value : algebra.Summary)
    (hvalue : value ∈ decision.leaves)
    : lawful.le value (decision.collapse algebra) := by
  induction decision with
  | leaf summary =>
      simp [leaves] at hvalue
      subst value
      exact lawful.le_refl summary
  | split test onFalse onTrue ihFalse ihTrue =>
      simp only [leaves, List.mem_append] at hvalue
      rcases hvalue with hvalue | hvalue
      · exact lawful.le_trans _ _ _ (ihFalse hvalue) (lawful.le_join_left _ _)
      · exact lawful.le_trans _ _ _ (ihTrue hvalue) (lawful.le_join_right _ _)
  | join left right ihLeft ihRight =>
      simp only [leaves, List.mem_append] at hvalue
      rcases hvalue with hvalue | hvalue
      · exact lawful.le_trans _ _ _ (ihLeft hvalue) (lawful.le_join_left _ _)
      · exact lawful.le_trans _ _ _ (ihRight hvalue) (lawful.le_join_right _ _)

theorem collapse_le_of_leaves (algebra : Algebra) (lawful : algebra.Lawful)
    (hjoinUpper
      : ∀ left right upper,
          lawful.le left upper
          -> lawful.le right upper
          -> lawful.le (algebra.join left right) upper)
    (decision : BooleanDecision algebra.Summary) (upper : algebra.Summary)
    (hleaves : ∀ value, value ∈ decision.leaves -> lawful.le value upper)
    : lawful.le (decision.collapse algebra) upper := by
  induction decision with
  | leaf value => exact hleaves value (by simp [leaves])
  | split test onFalse onTrue ihFalse ihTrue =>
      apply hjoinUpper
      · exact ihFalse (fun value hvalue => hleaves value (by simp [leaves, hvalue]))
      · exact ihTrue (fun value hvalue => hleaves value (by simp [leaves, hvalue]))
  | join left right ihLeft ihRight =>
      apply hjoinUpper
      · exact ihLeft (fun value hvalue => hleaves value (by simp [leaves, hvalue]))
      · exact ihRight (fun value hvalue => hleaves value (by simp [leaves, hvalue]))

theorem collapse_select_le (algebra : Algebra) (lawful : algebra.Lawful)
    (hjoinUpper
      : ∀ left right upper,
          lawful.le left upper
          -> lawful.le right upper
          -> lawful.le (algebra.join left right) upper)
    (variableValues : VariableValues) (decision : BooleanDecision algebra.Summary)
    : lawful.le ((select variableValues decision).collapse algebra)
        (decision.collapse algebra) := by
  induction decision with
  | leaf summary => exact lawful.le_refl summary
  | split test onFalse onTrue ihFalse ihTrue =>
      by_cases hselected : selectedValue variableValues test
      · simpa [select, collapse, hselected] using
          lawful.le_trans _ _ _ ihTrue (lawful.le_join_right _ _)
      · simpa [select, collapse, hselected] using
          lawful.le_trans _ _ _ ihFalse (lawful.le_join_left _ _)
  | join left right ihLeft ihRight =>
      simp only [select, collapse]
      apply hjoinUpper
      · exact lawful.le_trans _ _ _ ihLeft (lawful.le_join_left _ _)
      · exact lawful.le_trans _ _ _ ihRight (lawful.le_join_right _ _)

theorem Refines.collapse_le (algebra : Algebra) (lawful : algebra.Lawful)
    (hjoinUpper
      : ∀ left right upper,
          lawful.le left upper
          -> lawful.le right upper
          -> lawful.le (algebra.join left right) upper)
    (variableValues : VariableValues)
    {resolved symbolic : BooleanDecision algebra.Summary}
    (hrefines : Refines variableValues resolved symbolic)
    : lawful.le (resolved.collapse algebra) (symbolic.collapse algebra) := by
  apply collapse_le_of_leaves algebra lawful hjoinUpper resolved _
  intro value hvalue
  apply lawful.le_trans _ ((select variableValues symbolic).collapse algebra) _
  · exact le_collapse_of_mem algebra lawful (select variableValues symbolic) value
      (hrefines.leaves value hvalue)
  · exact collapse_select_le algebra lawful hjoinUpper variableValues symbolic

private theorem join_mono_of_le (algebra : Algebra) (lawful : algebra.Lawful)
    (hjoinUpper
      : ∀ left right upper,
          lawful.le left upper
          -> lawful.le right upper
          -> lawful.le (algebra.join left right) upper)
    {left lower right upper : algebra.Summary}
    (hleft : lawful.le left lower) (hright : lawful.le right upper)
    : lawful.le (algebra.join left right) (algebra.join lower upper) := by
  apply hjoinUpper
  · exact lawful.le_trans _ _ _ hleft (lawful.le_join_left _ _)
  · exact lawful.le_trans _ _ _ hright (lawful.le_join_right _ _)

theorem collapse_map_le_of_splitFree (algebra : Algebra) (lawful : algebra.Lawful)
    (hjoinUpper
      : ∀ left right upper,
          lawful.le left upper
          -> lawful.le right upper
          -> lawful.le (algebra.join left right) upper)
    (transform : algebra.Summary -> algebra.Summary)
    (hjoin
      : ∀ left right,
          lawful.le (transform (algebra.join left right))
            (algebra.join (transform left) (transform right)))
    {decision : BooleanDecision algebra.Summary} (hfree : decision.SplitFree)
    : lawful.le (transform (decision.collapse algebra))
        ((decision.map transform).collapse algebra) := by
  induction decision with
  | leaf => exact lawful.le_refl _
  | split => contradiction
  | join left right ihLeft ihRight =>
      apply lawful.le_trans _
        (algebra.join (transform (left.collapse algebra))
          (transform (right.collapse algebra)))
      · exact hjoin _ _
      · exact join_mono_of_le algebra lawful hjoinUpper
          (ihLeft hfree.1) (ihRight hfree.2)

private theorem combine_join_right_le (algebra : Algebra) (lawful : algebra.Lawful)
    (hcombine
      : ∀ left right other,
          lawful.le (algebra.combine (algebra.join left right) other)
            (algebra.join (algebra.combine left other) (algebra.combine right other)))
    (other left right : algebra.Summary)
    : lawful.le (algebra.combine other (algebra.join left right))
        (algebra.join (algebra.combine other left) (algebra.combine other right)) := by
  rw [lawful.combine_comm other (algebra.join left right)]
  apply lawful.le_trans _
    (algebra.join (algebra.combine left other) (algebra.combine right other))
  · exact hcombine left right other
  · rw [lawful.combine_comm left other, lawful.combine_comm right other]
    exact lawful.le_refl _

theorem collapse_zipWith_combine_le_of_splitFree (algebra : Algebra)
    (lawful : algebra.Lawful)
    (hjoinUpper
      : ∀ left right upper,
          lawful.le left upper
          -> lawful.le right upper
          -> lawful.le (algebra.join left right) upper)
    (hcombine
      : ∀ left right other,
          lawful.le (algebra.combine (algebra.join left right) other)
            (algebra.join (algebra.combine left other) (algebra.combine right other)))
    (variableOrder : BooleanVariableNames)
    {left right : BooleanDecision algebra.Summary}
    (hleft : left.SplitFree) (hright : right.SplitFree)
    : lawful.le (algebra.combine (left.collapse algebra) (right.collapse algebra))
        ((BooleanDecision.zipWith variableOrder algebra.combine left right).collapse
          algebra) := by
  induction left generalizing right with
  | leaf left =>
      rw [BooleanDecision.zipWith]
      exact collapse_map_le_of_splitFree algebra lawful hjoinUpper (algebra.combine left)
        (combine_join_right_le algebra lawful hcombine left) hright
  | split => contradiction
  | join leftFirst leftSecond ihFirst ihSecond =>
      cases right with
      | leaf right =>
          have hzip :
              BooleanDecision.zipWith variableOrder algebra.combine
                  (.join leftFirst leftSecond) (.leaf right)
                = (BooleanDecision.join leftFirst leftSecond).map
                    (fun value => algebra.combine value right) := by
            rw [BooleanDecision.zipWith] <;> simp
          rw [hzip]
          exact collapse_map_le_of_splitFree algebra lawful hjoinUpper
            (fun value => algebra.combine value right) (fun first second =>
              hcombine first second right) hleft
      | split => contradiction
      | join rightFirst rightSecond =>
          have hzip :
              BooleanDecision.zipWith variableOrder algebra.combine
                  (.join leftFirst leftSecond) (.join rightFirst rightSecond)
                = .join
                    (BooleanDecision.zipWith variableOrder algebra.combine leftFirst
                      (.join rightFirst rightSecond))
                    (BooleanDecision.zipWith variableOrder algebra.combine leftSecond
                      (.join rightFirst rightSecond)) := by
            rw [BooleanDecision.zipWith] <;> simp
          rw [hzip]
          apply lawful.le_trans _
            (algebra.join
              (algebra.combine (leftFirst.collapse algebra)
                ((BooleanDecision.join rightFirst rightSecond).collapse algebra))
              (algebra.combine (leftSecond.collapse algebra)
                ((BooleanDecision.join rightFirst rightSecond).collapse algebra)))
          · exact hcombine _ _ _
          · exact join_mono_of_le algebra lawful hjoinUpper
              (ihFirst hleft.1 hright) (ihSecond hleft.2 hright)

theorem collapse_joinMap (algebra : Algebra) (items : List α)
    (summarize : ∀ item, item ∈ items -> BooleanDecision algebra.Summary)
    : (BooleanDecision.joinMap algebra items summarize).collapse algebra
      = TreeSummary.joinMap algebra items
          fun item hitem => (summarize item hitem).collapse algebra := by
  cases items with
  | nil => simp [BooleanDecision.joinMap, TreeSummary.joinMap,
      BooleanDecision.collapse]
  | cons item rest =>
      cases rest with
      | nil => simp [BooleanDecision.joinMap, TreeSummary.joinMap]
      | cons next tail =>
          rw [BooleanDecision.joinMap, TreeSummary.joinMap,
            BooleanDecision.collapse]
          exact congrArg (algebra.join ((summarize item (by simp)).collapse algebra))
            (collapse_joinMap algebra (next :: tail)
              (fun candidate hcandidate => summarize candidate (by simp [hcandidate])))

theorem combineMap_splitFree (algebra : Algebra)
    (variableOrder : BooleanVariableNames) (items : List α)
    (summarize : ∀ item, item ∈ items -> BooleanDecision algebra.Summary)
    (hfree : ∀ item hitem, (summarize item hitem).SplitFree)
    : (BooleanDecision.combineMap algebra variableOrder items summarize).SplitFree := by
  induction items with
  | nil => simp [BooleanDecision.combineMap, BooleanDecision.SplitFree]
  | cons item rest ih =>
      rw [BooleanDecision.combineMap]
      exact BooleanDecision.zipWith_splitFree variableOrder algebra.combine
        (hfree item (by simp))
        (ih
          (fun candidate hcandidate => summarize candidate (by simp [hcandidate]))
              (fun candidate hcandidate => hfree candidate (by simp [hcandidate])))

theorem combineMap_congr_orders (algebra : Algebra)
    (leftOrder rightOrder : BooleanVariableNames) (items : List α)
    (left right : ∀ item, item ∈ items -> BooleanDecision algebra.Summary)
    (hitems : ∀ item hitem, left item hitem = right item hitem)
    (hfree : ∀ item hitem, (right item hitem).SplitFree)
    : BooleanDecision.combineMap algebra leftOrder items left
      = BooleanDecision.combineMap algebra rightOrder items right := by
  induction items with
  | nil => simp [BooleanDecision.combineMap]
  | cons item rest ih =>
      rw [BooleanDecision.combineMap, BooleanDecision.combineMap,
        hitems item (by simp)]
      have hrest := ih
        (fun candidate hcandidate => left candidate (by simp [hcandidate]))
        (fun candidate hcandidate => right candidate (by simp [hcandidate]))
        (fun candidate hcandidate => hitems candidate (by simp [hcandidate]))
        (fun candidate hcandidate => hfree candidate (by simp [hcandidate]))
      rw [hrest]
      exact zipWith_eq_of_splitFree leftOrder rightOrder algebra.combine
        (hfree item (by simp))
        (combineMap_splitFree algebra rightOrder rest
          (fun candidate hcandidate => right candidate (by simp [hcandidate]))
          (fun candidate hcandidate => hfree candidate (by simp [hcandidate])))

theorem joinMap_congr (algebra : Algebra) (items : List α)
    (left right : ∀ item, item ∈ items -> BooleanDecision algebra.Summary)
    (hitems : ∀ item hitem, left item hitem = right item hitem)
    : BooleanDecision.joinMap algebra items left
      = BooleanDecision.joinMap algebra items right := by
  cases items with
  | nil => simp [BooleanDecision.joinMap]
  | cons item rest =>
      cases rest with
      | nil => simpa [BooleanDecision.joinMap] using hitems item (by simp)
      | cons next tail =>
          rw [BooleanDecision.joinMap, BooleanDecision.joinMap,
            hitems item (by simp)]
          exact congrArg (BooleanDecision.join (right item (by simp)))
            (joinMap_congr algebra (next :: tail)
              (fun candidate hcandidate => left candidate (by simp [hcandidate]))
              (fun candidate hcandidate => right candidate (by simp [hcandidate]))
              (fun candidate hcandidate => hitems candidate (by simp [hcandidate])))
termination_by items.length

theorem joinMap_splitFree (algebra : Algebra)
    (items : List α)
    (summarize : ∀ item, item ∈ items -> BooleanDecision algebra.Summary)
    (hfree : ∀ item hitem, (summarize item hitem).SplitFree)
    : (BooleanDecision.joinMap algebra items summarize).SplitFree := by
  cases items with
  | nil => simp [BooleanDecision.joinMap, BooleanDecision.SplitFree]
  | cons item rest =>
      cases rest with
      | nil => simpa [BooleanDecision.joinMap] using hfree item (by simp)
      | cons next tail =>
          rw [BooleanDecision.joinMap]
          exact ⟨hfree item (by simp),
            joinMap_splitFree algebra (next :: tail)
              (fun candidate hcandidate => summarize candidate (by simp [hcandidate]))
              (fun candidate hcandidate => hfree candidate (by simp [hcandidate]))⟩

private theorem combineMap_congr (algebra : Algebra) (items : List α)
    (left right : ∀ item, item ∈ items -> algebra.Summary)
    (hitems : ∀ item hitem, left item hitem = right item hitem)
    : TreeSummary.combineMap algebra items left
      = TreeSummary.combineMap algebra items right := by
  induction items with
  | nil => simp [TreeSummary.combineMap]
  | cons item rest ih =>
      rw [TreeSummary.combineMap, TreeSummary.combineMap, hitems item (by simp)]
      exact congrArg (algebra.combine (right item (by simp)))
        (ih
          (fun candidate hcandidate => left candidate (by simp [hcandidate]))
          (fun candidate hcandidate => right candidate (by simp [hcandidate]))
          (fun candidate hcandidate => hitems candidate (by simp [hcandidate])))

private theorem combineMap_mono (algebra : Algebra) (lawful : algebra.Lawful)
    (items : List α)
    (lower upper : ∀ item, item ∈ items -> algebra.Summary)
    (hitems : ∀ item hitem, lawful.le (lower item hitem) (upper item hitem))
    : lawful.le (TreeSummary.combineMap algebra items lower)
        (TreeSummary.combineMap algebra items upper) := by
  induction items with
  | nil => simpa [TreeSummary.combineMap] using lawful.le_refl algebra.empty
  | cons item rest ih =>
      rw [TreeSummary.combineMap, TreeSummary.combineMap]
      apply lawful.combine_mono
      · exact hitems item (by simp)
      · exact ih
          (fun candidate hcandidate => lower candidate (by simp [hcandidate]))
          (fun candidate hcandidate => upper candidate (by simp [hcandidate]))
          (fun candidate hcandidate => hitems candidate (by simp [hcandidate]))

theorem collapse_combineMap_le_of_splitFree (algebra : Algebra)
    (lawful : algebra.Lawful)
    (hjoinUpper
      : ∀ left right upper,
          lawful.le left upper
          -> lawful.le right upper
          -> lawful.le (algebra.join left right) upper)
    (hcombine
      : ∀ left right other,
          lawful.le (algebra.combine (algebra.join left right) other)
            (algebra.join (algebra.combine left other) (algebra.combine right other)))
    (variableOrder : BooleanVariableNames) (items : List α)
    (summarize : ∀ item, item ∈ items -> BooleanDecision algebra.Summary)
    (hfree : ∀ item hitem, (summarize item hitem).SplitFree)
    : lawful.le
        (TreeSummary.combineMap algebra items
          fun item hitem => (summarize item hitem).collapse algebra)
        ((BooleanDecision.combineMap algebra variableOrder items summarize).collapse
          algebra) := by
  induction items with
  | nil =>
      simpa [TreeSummary.combineMap, BooleanDecision.combineMap,
        BooleanDecision.collapse] using lawful.le_refl algebra.empty
  | cons item rest ih =>
      rw [TreeSummary.combineMap, BooleanDecision.combineMap]
      apply lawful.le_trans _
        (algebra.combine ((summarize item (by simp)).collapse algebra)
          ((BooleanDecision.combineMap algebra variableOrder rest
            fun candidate hcandidate =>
              summarize candidate (by simp [hcandidate])).collapse algebra))
      · apply lawful.combine_mono
        · exact lawful.le_refl _
        · exact ih
            (fun candidate hcandidate => summarize candidate (by simp [hcandidate]))
            (fun candidate hcandidate => hfree candidate (by simp [hcandidate]))
      · exact collapse_zipWith_combine_le_of_splitFree algebra lawful hjoinUpper hcombine
          variableOrder (hfree item (by simp))
          (BooleanDecision.combineMap_splitFree algebra variableOrder rest
            (fun candidate hcandidate => summarize candidate (by simp [hcandidate]))
            (fun candidate hcandidate => hfree candidate (by simp [hcandidate])))

end BooleanDecision
end Internal

theorem CaseCursor.BooleanEnvironment.concrete_statusForVariable
    (variableValues : VariableValues) (variableName : Name)
    : (CaseCursor.BooleanEnvironment.concrete variableValues).statusForVariable
        variableName
      = match inputValueBoolean? variableValues (.variable variableName) with
        | some value => some value
        | none => some false := by
  unfold CaseCursor.BooleanEnvironment.statusForVariable CaseCursor.BooleanEnvironment.variableValues
  cases hvalue : inputValueBoolean? variableValues (.variable variableName) with
  | some value => rfl
  | none => rfl

private def CaseCursor.BooleanEnvironment.IsSymbolic
    : CaseCursor.BooleanEnvironment -> Prop
  | .symbolic _values => True
  | .concrete _values => False

private theorem CaseCursor.BooleanEnvironment.IsSymbolic.assign
    {environment : CaseCursor.BooleanEnvironment} (hsymbolic : environment.IsSymbolic)
    (variableName : Name) (value : Bool)
    : (environment.assign variableName value).IsSymbolic := by
  cases environment <;> simp_all [CaseCursor.BooleanEnvironment.IsSymbolic,
    CaseCursor.BooleanEnvironment.assign]

private def CaseCursor.BooleanEnvironment.Realizes
    (environment : CaseCursor.BooleanEnvironment) (variableValues : VariableValues)
    : Prop :=
  ∀ variableName value,
    environment.statusForVariable variableName = some value
    -> (inputValueBoolean? variableValues (.variable variableName)).getD false = value

private theorem CaseCursor.BooleanEnvironment.unresolved_realizes
    (variableValues : VariableValues)
    : CaseCursor.BooleanEnvironment.unresolved.Realizes variableValues := by
  intro variableName value hstatus
  simp [CaseCursor.BooleanEnvironment.unresolved, CaseCursor.BooleanEnvironment.statusForVariable,
    CaseCursor.BooleanEnvironment.variableValues, inputValueBoolean?, lookupVariableValue?]
    at hstatus

private theorem CaseCursor.BooleanEnvironment.Realizes.assign
    {environment : CaseCursor.BooleanEnvironment} {variableValues : VariableValues}
    (hrealizes : environment.Realizes variableValues) (hsymbolic : environment.IsSymbolic)
    (variableName : Name) (value : Bool)
    (hvalue
      : (inputValueBoolean? variableValues (.variable variableName)).getD false = value)
    : (environment.assign variableName value).Realizes variableValues := by
  cases environment with
  | concrete values => contradiction
  | symbolic values =>
      intro candidate candidateValue hstatus
      by_cases heq : candidate = variableName
      · subst candidate
        simp [CaseCursor.BooleanEnvironment.assign, CaseCursor.BooleanEnvironment.statusForVariable,
          CaseCursor.BooleanEnvironment.variableValues, inputValueBoolean?, lookupVariableValue?,
          ConstInputValue.toInputValue, InputValue.staticBoolean?] at hstatus
        subst candidateValue
        exact hvalue
      · have hne : variableName ≠ candidate := fun equal => heq equal.symm
        apply hrealizes candidate candidateValue
        simpa [CaseCursor.BooleanEnvironment.assign, CaseCursor.BooleanEnvironment.statusForVariable,
          CaseCursor.BooleanEnvironment.variableValues, inputValueBoolean?, lookupVariableValue?,
          heq, hne] using hstatus

private def NamedFieldsBooleanFree (fields : List NamedField) : Prop :=
  ∀ namedField,
    namedField ∈ fields
    -> SelectionConditions.selectionSetBooleanVariables namedField.field.selectionSet = []

private def FieldGroupBooleanFree (group : ConditionTree.FieldGroup) : Prop :=
  ∀ field,
    field ∈ group.fields
    -> SelectionConditions.selectionSetBooleanVariables field.selectionSet = []

private def FieldGroupsBooleanFree (groups : List ConditionTree.FieldGroup) : Prop :=
  ∀ group, group ∈ groups -> FieldGroupBooleanFree group

private def CollectedFieldGroupsBooleanFree (groups : List CollectedFieldGroup) : Prop :=
  ∀ group,
    group ∈ groups
    -> SelectionConditions.selectionSetBooleanVariables group.mergedSelectionSet = []

private def CaseCursorBooleanFree (cursor : CaseCursor) : Prop :=
  NamedFieldsBooleanFree cursor.namedFields
  ∧ conditionTreeBranchesBooleanVariables cursor.pendingBranches = []

private theorem selectionSetBooleanVariables_append (left right : List Selection)
    : SelectionConditions.selectionSetBooleanVariables (left ++ right)
      = SelectionConditions.selectionSetBooleanVariables left
        ++ SelectionConditions.selectionSetBooleanVariables right := by
  induction left with
  | nil => rfl
  | cons selection rest ih =>
      simp [SelectionConditions.selectionSetBooleanVariables, ih, List.append_assoc]

private theorem conditionTreeBranchesBooleanVariables_append
    (left right : List (Branch Tree))
    : conditionTreeBranchesBooleanVariables (left ++ right)
      = conditionTreeBranchesBooleanVariables left
        ++ conditionTreeBranchesBooleanVariables right := by
  induction left with
  | nil => simp [conditionTreeBranchesBooleanVariables]
  | cons branch rest ih =>
      rcases branch with ⟨condition, body⟩
      rw [List.cons_append, conditionTreeBranchesBooleanVariables.eq_def,
        conditionTreeBranchesBooleanVariables.eq_def]
      change (match condition with
                | .typeCondition _ => []
                | .booleanLiteral literal => [literal.variableName])
                ++ conditionTreeBooleanVariables body
                ++ conditionTreeBranchesBooleanVariables (rest ++ right)
              = ((match condition with
                  | .typeCondition _ => []
                  | .booleanLiteral literal => [literal.variableName])
                  ++ conditionTreeBooleanVariables body
                  ++ conditionTreeBranchesBooleanVariables rest)
                ++ conditionTreeBranchesBooleanVariables right
      rw [ih]
      simp [List.append_assoc]

private theorem fieldGroupsBooleanFree_addFieldWithResponseName
    {groups : List ConditionTree.FieldGroup} (hgroups : FieldGroupsBooleanFree groups)
    (responseName : Name) (field : Field)
    (hfield : SelectionConditions.selectionSetBooleanVariables field.selectionSet = [])
    : FieldGroupsBooleanFree (addFieldWithResponseName responseName field groups) := by
  induction groups with
  | nil =>
      intro group hgroup candidate hcandidate
      simp only [addFieldWithResponseName, List.mem_singleton] at hgroup
      subst group
      simp only [FieldGroup.fields, List.mem_cons, List.mem_nil_iff, or_false] at hcandidate
      subst candidate
      exact hfield
  | cons headGroup rest ih =>
      rw [addFieldWithResponseName]
      split
      · intro candidateGroup hcandidateGroup candidateField hcandidateField
        simp only [List.mem_cons] at hcandidateGroup
        rcases hcandidateGroup with hcandidateGroup | hcandidateGroup
        · subst candidateGroup
          simp only [FieldGroup.fields, List.mem_cons, List.mem_append,
            List.not_mem_nil, or_false] at hcandidateField
          rcases hcandidateField with hcandidateField | hcandidateField
          · subst candidateField
            exact hgroups headGroup (by simp) headGroup.first (by
              simp [FieldGroup.fields])
          · rcases hcandidateField with hcandidateField | hcandidateField
            · exact hgroups headGroup (by simp) candidateField (by
                simp [FieldGroup.fields, hcandidateField])
            · exact hcandidateField ▸ hfield
        · exact hgroups candidateGroup (by simp [hcandidateGroup]) candidateField
            hcandidateField
      · intro candidateGroup hcandidateGroup
        simp only [List.mem_cons] at hcandidateGroup
        rcases hcandidateGroup with hcandidateGroup | hcandidateGroup
        · subst candidateGroup
          exact hgroups headGroup (by simp)
        · exact ih
            (fun candidate hcandidate => hgroups candidate (by simp [hcandidate]))
            candidateGroup hcandidateGroup

private theorem collectFieldGroups_booleanFree
    {fields : List NamedField} (hfields : NamedFieldsBooleanFree fields)
    : FieldGroupsBooleanFree (ConditionTree.collectFieldGroups fields) := by
  unfold ConditionTree.collectFieldGroups
  have hfold : ∀ rest groups,
      NamedFieldsBooleanFree rest
      -> FieldGroupsBooleanFree groups
      -> FieldGroupsBooleanFree
          (rest.foldl (fun current field => addFieldToGroups field current) groups) := by
    intro rest
    induction rest with
    | nil => exact fun groups _hrest hgroups => hgroups
    | cons namedField tail ih =>
        intro groups hrest hgroups
        rw [List.foldl_cons]
        apply ih _
        · intro candidate hcandidate
          exact hrest candidate (by simp [hcandidate])
        · exact fieldGroupsBooleanFree_addFieldWithResponseName hgroups
            namedField.responseName
            namedField.field (hrest namedField (by simp))
  exact hfold fields [] hfields (by intro group hgroup; simp at hgroup)

private theorem fieldGroupBooleanVariables_mergedSelectionSet
    (group : ConditionTree.FieldGroup) (hgroup : FieldGroupBooleanFree group)
    : SelectionConditions.selectionSetBooleanVariables group.mergedSelectionSet = [] := by
  unfold ConditionTree.FieldGroup.mergedSelectionSet SelectionSet.mergeSelectionSets
    ConditionTree.FieldGroup.selections
  have hfields : ∀ fields : List Field,
      (∀ field, field ∈ fields
        -> SelectionConditions.selectionSetBooleanVariables field.selectionSet = [])
      -> SelectionConditions.selectionSetBooleanVariables
          (fields.map (Field.toSelection group.responseName)
            |>.flatMap Selection.subselections) = [] := by
    intro fields hfree
    induction fields with
    | nil => rfl
    | cons field rest ih =>
        simp only [List.map_cons, List.flatMap_cons, Field.toSelection,
          Selection.subselections]
        rw [selectionSetBooleanVariables_append, hfree field (by simp)]
        simp only [List.nil_append]
        exact ih (fun candidate hcandidate => hfree candidate (by simp [hcandidate]))
  exact hfields group.fields hgroup

private theorem CaseCursor.fieldGroups_booleanFree
    {cursor : CaseCursor} (hcursor : CaseCursorBooleanFree cursor)
    (inheritedBooleanCondition : List BooleanLiteral)
    (possibleTypes : PossibleTypeRegion)
    : CollectedFieldGroupsBooleanFree
        (cursor.fieldGroups inheritedBooleanCondition possibleTypes) := by
  intro group hgroup
  unfold CaseCursor.fieldGroups TreeSummary.fieldGroupsWithContext at hgroup
  rw [List.mem_map] at hgroup
  rcases hgroup with ⟨source, hsource, rfl⟩
  exact fieldGroupBooleanVariables_mergedSelectionSet source
    ((collectFieldGroups_booleanFree hcursor.1) source hsource)

private theorem CaseCursor.skipBranch_booleanFree
    {cursor : CaseCursor} {branch : Branch Tree} {rest : List (Branch Tree)}
    (hcursor : CaseCursorBooleanFree cursor)
    (hbranches : cursor.pendingBranches = branch :: rest)
    : CaseCursorBooleanFree (cursor.skipBranch rest) := by
  constructor
  · exact hcursor.1
  · change conditionTreeBranchesBooleanVariables rest = []
    have hsupport := hcursor.2
    rw [hbranches] at hsupport
    rcases branch with ⟨condition, body⟩
    cases condition <;>
      simp_all [conditionTreeBranchesBooleanVariables]

private theorem CaseCursor.selectBranch_booleanFree
    {cursor : CaseCursor} {branch : Branch Tree} {rest : List (Branch Tree)}
    (hcursor : CaseCursorBooleanFree cursor)
    (hbranches : cursor.pendingBranches = branch :: rest)
    (hcondition : ∃ typeName, branch.condition = .typeCondition typeName)
    : CaseCursorBooleanFree (cursor.selectBranch branch.body rest) := by
  rcases hcondition with ⟨typeName, hcondition⟩
  rcases branch with ⟨condition, body⟩
  simp only at hcondition
  subst condition
  have hsupport := hcursor.2
  rw [hbranches] at hsupport
  simp only [conditionTreeBranchesBooleanVariables, List.nil_append] at hsupport
  have hbody : conditionTreeBooleanVariables body = [] :=
    (List.append_eq_nil_iff.mp hsupport).1
  have hrest : conditionTreeBranchesBooleanVariables rest = [] :=
    (List.append_eq_nil_iff.mp hsupport).2
  rcases body with ⟨bodyCondition, bodyFields, bodyBranches⟩
  rw [conditionTreeBooleanVariables.eq_def] at hbody
  change
    (bodyFields.flatMap fun group =>
        group.fields.flatMap fun field =>
          SelectionConditions.selectionSetBooleanVariables field.selectionSet)
      ++ conditionTreeBranchesBooleanVariables bodyBranches = [] at hbody
  have hbodyFields := (List.append_eq_nil_iff.mp hbody).1
  have hbodyBranches := (List.append_eq_nil_iff.mp hbody).2
  constructor
  · intro namedField hnamedField
    have hnamedField :
        namedField ∈ cursor.namedFields ++ CaseCursor.localNamedFields
          { condition := bodyCondition, fields := bodyFields, branches := bodyBranches } := by
      simpa [CaseCursor.selectBranch, CaseCursor.namedFields] using hnamedField
    rw [List.mem_append] at hnamedField
    rcases hnamedField with hnamedField | hnamedField
    · exact hcursor.1 namedField hnamedField
    · unfold CaseCursor.localNamedFields at hnamedField
      simp only [List.mem_flatMap, List.mem_map] at hnamedField
      rcases hnamedField with ⟨group, hgroup, field, hfield, rfl⟩
      have hgroupFree := (List.flatMap_eq_nil_iff.mp hbodyFields) group hgroup
      simp only [List.flatMap_eq_nil_iff] at hgroupFree
      exact hgroupFree field hfield
  · change conditionTreeBranchesBooleanVariables (bodyBranches ++ rest) = []
    rw [conditionTreeBranchesBooleanVariables_append]
    simp [hbodyBranches, hrest]

private theorem CaseCursor.booleanBranch_impossible
    {cursor : CaseCursor} {branch : Branch Tree} {rest : List (Branch Tree)}
    (hcursor : CaseCursorBooleanFree cursor)
    (hbranches : cursor.pendingBranches = branch :: rest)
    (literal : BooleanLiteral)
    (hcondition : branch.condition = .booleanLiteral literal)
    : False := by
  have hsupport := hcursor.2
  rw [hbranches] at hsupport
  rcases branch with ⟨condition, body⟩
  simp only at hcondition
  subst condition
  simp [conditionTreeBranchesBooleanVariables] at hsupport

private theorem CaseCursor.ofConditionTree_booleanFree
    (tree : Tree) (htree : conditionTreeBooleanVariables tree = [])
    : CaseCursorBooleanFree (.ofConditionTree tree) := by
  rcases tree with ⟨condition, fields, branches⟩
  rw [conditionTreeBooleanVariables.eq_def] at htree
  change
    (fields.flatMap fun group =>
        group.fields.flatMap fun field =>
          SelectionConditions.selectionSetBooleanVariables field.selectionSet)
      ++ conditionTreeBranchesBooleanVariables branches = [] at htree
  have hfields := (List.append_eq_nil_iff.mp htree).1
  have hbranches := (List.append_eq_nil_iff.mp htree).2
  constructor
  · intro namedField hnamedField
    have hnamedField : namedField ∈ CaseCursor.localNamedFields
        { condition, fields, branches } := by
      simpa [CaseCursor.ofConditionTree, CaseCursor.namedFields] using hnamedField
    unfold CaseCursor.localNamedFields at hnamedField
    simp only [List.mem_flatMap, List.mem_map] at hnamedField
    rcases hnamedField with ⟨group, hgroup, field, hfield, rfl⟩
    have hgroupFree := (List.flatMap_eq_nil_iff.mp hfields) group hgroup
    exact (List.flatMap_eq_nil_iff.mp hgroupFree) field hfield
  · exact hbranches

theorem CaseCursor.summarizeDecisionWithPruning_nil_values
    (algebra : Algebra) (schema : Schema) (variableOrder : BooleanVariableNames)
    (inheritedBooleanCondition caseCondition : List BooleanLiteral)
    (cursor : CaseCursor)
    (possibleTypes : PossibleTypeRegion) (environment : CaseCursor.BooleanEnvironment)
    (pruningValues : VariableValues := environment.pruningValues)
    (hbranches : cursor.pendingBranches = [])
    : cursor.summarizeDecisionWithPruning algebra schema variableOrder
        inheritedBooleanCondition caseCondition possibleTypes environment pruningValues
      = CaseCursor.summarizeFieldGroupsDecisionWithPruning algebra schema variableOrder
          (cursor.fieldGroups
            (extendBooleanCondition inheritedBooleanCondition caseCondition)
            possibleTypes)
          environment pruningValues := by
  rcases cursor with ⟨namedFields, pendingBranches⟩
  change pendingBranches = [] at hbranches
  subst pendingBranches
  rw [CaseCursor.summarizeDecisionWithPruning.eq_1]

theorem CaseCursor.summarizeDecisionWithPruning_cons_values
    (algebra : Algebra) (schema : Schema) (variableOrder : BooleanVariableNames)
    (inheritedBooleanCondition caseCondition : List BooleanLiteral)
    (cursor : CaseCursor)
    (possibleTypes : PossibleTypeRegion) (environment : CaseCursor.BooleanEnvironment)
    (pruningValues : VariableValues := environment.pruningValues)
    (branch : Branch Tree) (rest : List (Branch Tree))
    (hbranches : cursor.pendingBranches = branch :: rest)
    : cursor.summarizeDecisionWithPruning algebra schema variableOrder
        inheritedBooleanCondition caseCondition possibleTypes environment pruningValues
      = match branch.condition with
        | .typeCondition _typeName =>
            BooleanDecision.joinMap algebra
              (possibleTypeRegions possibleTypes [branch.body.condition.possibleTypes])
              fun region _hregion =>
                if possibleTypesSubset region branch.body.condition.possibleTypes then
                  (cursor.selectBranch branch.body rest).summarizeDecisionWithPruning
                    algebra schema variableOrder inheritedBooleanCondition caseCondition
                    region environment pruningValues
                else
                  (cursor.skipBranch rest).summarizeDecisionWithPruning algebra schema
                    variableOrder inheritedBooleanCondition caseCondition region
                    environment pruningValues
        | .booleanLiteral literal =>
            match environment.statusForVariable literal.variableName with
            | some value =>
                let selectedLiteral :=
                  if value then
                    BooleanLiteral.positive literal.variableName
                  else
                    BooleanLiteral.negative literal.variableName
                (cursor.resolveBooleanBranch branch.body rest literal
                  value).summarizeDecisionWithPruning
                  algebra schema variableOrder inheritedBooleanCondition
                  (selectedLiteral :: caseCondition) possibleTypes environment
                  pruningValues
            | none =>
                .split literal.variableName
                  ((cursor.resolveBooleanBranch branch.body rest literal
                      false).summarizeDecisionWithPruning
                    algebra schema variableOrder inheritedBooleanCondition
                    (.negative literal.variableName :: caseCondition) possibleTypes
                    (environment.assign literal.variableName false) pruningValues)
                  ((cursor.resolveBooleanBranch branch.body rest literal
                      true).summarizeDecisionWithPruning
                    algebra schema variableOrder inheritedBooleanCondition
                    (.positive literal.variableName :: caseCondition) possibleTypes
                    (environment.assign literal.variableName true) pruningValues) := by
  rcases cursor with ⟨namedFields, pendingBranches⟩
  change pendingBranches = branch :: rest at hbranches
  subst pendingBranches
  rw [CaseCursor.summarizeDecisionWithPruning.eq_1]
  rfl

private theorem CaseCursor.summarizeDecisionWithPruning_refines_complete
    (algebra : Algebra) (schema : Schema) (variableOrder : BooleanVariableNames)
    (inheritedBooleanCondition caseCondition : List BooleanLiteral)
    (cursor : CaseCursor)
    (possibleTypes : PossibleTypeRegion) (environment : CaseCursor.BooleanEnvironment)
    (variableValues pruningValues : VariableValues)
    (hrealizes : environment.Realizes variableValues)
    (hsymbolic : environment.IsSymbolic)
    : BooleanDecision.Refines variableValues
        (cursor.summarizeDecisionWithPruning algebra schema variableOrder
          inheritedBooleanCondition caseCondition possibleTypes
          (CaseCursor.BooleanEnvironment.concrete variableValues) pruningValues)
        (cursor.summarizeDecisionWithPruning algebra schema variableOrder
          inheritedBooleanCondition caseCondition possibleTypes environment
          pruningValues) := by
  apply CaseCursor.summarizeDecisionWithPruning.induct schema pruningValues
    (motive1 := fun inherited caseCondition cursor possibleTypes environment =>
      ∀ variableValues,
        environment.Realizes variableValues
        -> environment.IsSymbolic
        -> BooleanDecision.Refines variableValues
            (cursor.summarizeDecisionWithPruning algebra schema variableOrder inherited
              caseCondition possibleTypes
              (CaseCursor.BooleanEnvironment.concrete variableValues) pruningValues)
            (cursor.summarizeDecisionWithPruning algebra schema variableOrder inherited
              caseCondition possibleTypes environment pruningValues))
    (motive2 := fun groups environment =>
      ∀ variableValues,
        environment.Realizes variableValues
        -> environment.IsSymbolic
        -> BooleanDecision.Refines variableValues
            (CaseCursor.summarizeFieldGroupsDecisionWithPruning algebra schema variableOrder groups
              (CaseCursor.BooleanEnvironment.concrete variableValues) pruningValues)
            (CaseCursor.summarizeFieldGroupsDecisionWithPruning algebra schema variableOrder groups
              environment pruningValues))
    (motive3 := fun group parentTypes environment =>
      ∀ variableValues,
        environment.Realizes variableValues
        -> environment.IsSymbolic
        -> BooleanDecision.Refines variableValues
            (CaseCursor.summarizeChildTypesDecisionWithPruning algebra schema variableOrder group
              parentTypes
              (CaseCursor.BooleanEnvironment.concrete variableValues) pruningValues)
            (CaseCursor.summarizeChildTypesDecisionWithPruning algebra schema variableOrder group
              parentTypes environment pruningValues))
  case case1 =>
    intro inherited caseCondition cursor possibleTypes environment
      hbranches ih variableValues hrealizes hsymbolic
    rw [CaseCursor.summarizeDecisionWithPruning_nil_values algebra schema variableOrder inherited
      caseCondition cursor possibleTypes environment pruningValues hbranches,
      CaseCursor.summarizeDecisionWithPruning_nil_values algebra schema variableOrder inherited
        caseCondition cursor possibleTypes
        (CaseCursor.BooleanEnvironment.concrete variableValues) pruningValues hbranches]
    exact ih variableValues hrealizes hsymbolic
  case case2 =>
    intro inherited caseCondition cursor possibleTypes environment branch rest
      hbranches typeName hcondition ihSelect ihSkip variableValues hrealizes hsymbolic
    rw [CaseCursor.summarizeDecisionWithPruning_cons_values algebra schema variableOrder inherited
      caseCondition cursor possibleTypes environment pruningValues branch rest
      hbranches,
      CaseCursor.summarizeDecisionWithPruning_cons_values algebra schema variableOrder inherited
        caseCondition cursor possibleTypes
        (CaseCursor.BooleanEnvironment.concrete variableValues) pruningValues branch rest
        hbranches]
    simp only [hcondition]
    apply BooleanDecision.Refines.joinMap algebra variableValues
    intro region hregion
    split
    · exact ihSelect region variableValues hrealizes hsymbolic
    · exact ihSkip region variableValues hrealizes hsymbolic
  case case3 =>
    intro inherited caseCondition cursor possibleTypes environment branch rest
      hbranches literal hcondition value hstatus selectedLiteral ih variableValues
      hrealizes hsymbolic
    have hknown := hrealizes literal.variableName value hstatus
    rw [CaseCursor.summarizeDecisionWithPruning_cons_values algebra schema variableOrder inherited
      caseCondition cursor possibleTypes environment pruningValues branch rest
      hbranches,
      CaseCursor.summarizeDecisionWithPruning_cons_values algebra schema variableOrder inherited
        caseCondition cursor possibleTypes
        (CaseCursor.BooleanEnvironment.concrete variableValues) pruningValues branch rest
        hbranches]
    simp only [hcondition, hstatus]
    rw [CaseCursor.BooleanEnvironment.concrete_statusForVariable]
    cases hvalue : inputValueBoolean? variableValues (.variable literal.variableName) with
    | none =>
        have hfalse : value = false := by simpa [hvalue] using hknown.symm
        subst value
        simp
        simpa [selectedLiteral, hvalue] using
          ih variableValues hrealizes hsymbolic
    | some actual =>
        have heq : actual = value := by simpa [hvalue] using hknown
        subst actual
        simp
        simpa [selectedLiteral, hvalue] using
          ih variableValues hrealizes hsymbolic
  case case4 =>
    intro inherited caseCondition cursor possibleTypes environment branch rest
      hbranches literal hcondition hstatus ihFalse ihTrue variableValues
      hrealizes hsymbolic
    rw [CaseCursor.summarizeDecisionWithPruning_cons_values algebra schema variableOrder inherited
      caseCondition cursor possibleTypes environment pruningValues branch rest
      hbranches,
      CaseCursor.summarizeDecisionWithPruning_cons_values algebra schema variableOrder inherited
        caseCondition cursor possibleTypes
        (CaseCursor.BooleanEnvironment.concrete variableValues) pruningValues branch rest
        hbranches]
    simp only [hcondition, hstatus]
    rw [CaseCursor.BooleanEnvironment.concrete_statusForVariable]
    cases hvalue : inputValueBoolean? variableValues (.variable literal.variableName) with
    | none =>
        have hrefines := ihFalse variableValues
          (hrealizes.assign hsymbolic literal.variableName false (by simp [hvalue]))
          (hsymbolic.assign literal.variableName false)
        exact BooleanDecision.Refines.of_select_eq variableValues
          (by simp [BooleanDecision.select, BooleanDecision.selectedValue, hvalue]) hrefines
    | some selected =>
        cases selected
        · simp only
          have hrefines := ihFalse variableValues
            (hrealizes.assign hsymbolic literal.variableName false (by simp [hvalue]))
            (hsymbolic.assign literal.variableName false)
          exact BooleanDecision.Refines.of_select_eq variableValues
            (by simp [BooleanDecision.select, BooleanDecision.selectedValue, hvalue]) hrefines
        · simp only
          have hrefines := ihTrue variableValues
            (hrealizes.assign hsymbolic literal.variableName true (by simp [hvalue]))
            (hsymbolic.assign literal.variableName true)
          exact BooleanDecision.Refines.of_select_eq variableValues
            (by simp [BooleanDecision.select, BooleanDecision.selectedValue, hvalue]) hrefines
  case case5 =>
    intro groups environment ih variableValues hrealizes hsymbolic
    simp only [CaseCursor.summarizeFieldGroupsDecisionWithPruning.eq_1]
    apply BooleanDecision.Refines.combineMap algebra variableValues variableOrder
    intro group hgroup
    exact BooleanDecision.Refines.map variableValues (algebra.field group)
      (ih group hgroup variableValues hrealizes hsymbolic)
  case case6 =>
    intro group parentTypes environment ih variableValues hrealizes hsymbolic
    simp only [CaseCursor.summarizeChildTypesDecisionWithPruning.eq_1]
    apply BooleanDecision.Refines.joinMap algebra variableValues
    intro childParentType hparentType
    exact ih childParentType variableValues hrealizes hsymbolic
  exact hrealizes
  exact hsymbolic

theorem CaseCursor.summarizeDecisionWithPruning_complete_splitFree
    (algebra : Algebra) (schema : Schema) (variableOrder : BooleanVariableNames)
    (inheritedBooleanCondition caseCondition : List BooleanLiteral)
    (cursor : CaseCursor)
    (possibleTypes : PossibleTypeRegion)
    (variableValues fixedVariableValues : VariableValues)
    : (CaseCursor.summarizeDecisionWithPruning algebra schema variableOrder
        inheritedBooleanCondition caseCondition cursor possibleTypes
        (CaseCursor.BooleanEnvironment.concrete variableValues)
        fixedVariableValues).SplitFree := by
  apply CaseCursor.summarizeDecisionWithPruning.induct schema fixedVariableValues
    (motive1 := fun inherited caseCondition cursor possibleTypes environment =>
      ∀ variableValues,
        environment = CaseCursor.BooleanEnvironment.concrete variableValues
        -> (CaseCursor.summarizeDecisionWithPruning algebra schema variableOrder inherited
          caseCondition cursor possibleTypes environment
          fixedVariableValues).SplitFree)
    (motive2 := fun groups environment =>
      ∀ variableValues,
        environment = CaseCursor.BooleanEnvironment.concrete variableValues
        -> (CaseCursor.summarizeFieldGroupsDecisionWithPruning algebra schema variableOrder groups
          environment fixedVariableValues).SplitFree)
    (motive3 := fun group parentTypes environment =>
      ∀ variableValues,
        environment = CaseCursor.BooleanEnvironment.concrete variableValues
        -> (CaseCursor.summarizeChildTypesDecisionWithPruning algebra schema variableOrder group
          parentTypes environment fixedVariableValues).SplitFree)
  case case1 =>
    intro inherited caseCondition cursor possibleTypes environment
      hbranches ih variableValues henvironment
    subst environment
    rw [CaseCursor.summarizeDecisionWithPruning_nil_values algebra schema variableOrder inherited
      caseCondition cursor possibleTypes
      (CaseCursor.BooleanEnvironment.concrete variableValues) fixedVariableValues hbranches]
    exact ih variableValues rfl
  case case2 =>
    intro inherited caseCondition cursor possibleTypes environment branch rest
      hbranches typeName hcondition ihSelect ihSkip variableValues henvironment
    subst environment
    rw [CaseCursor.summarizeDecisionWithPruning_cons_values algebra schema variableOrder inherited
      caseCondition cursor possibleTypes
      (CaseCursor.BooleanEnvironment.concrete variableValues) fixedVariableValues branch rest hbranches]
    simp only [hcondition]
    apply BooleanDecision.joinMap_splitFree
    intro region hregion
    split
    · exact ihSelect region variableValues rfl
    · exact ihSkip region variableValues rfl
  case case3 =>
    intro inherited caseCondition cursor possibleTypes environment branch rest
      hbranches literal hcondition value hstatus selectedLiteral ih variableValues
      henvironment
    subst environment
    rw [CaseCursor.summarizeDecisionWithPruning_cons_values algebra schema variableOrder inherited
      caseCondition cursor possibleTypes
      (CaseCursor.BooleanEnvironment.concrete variableValues) fixedVariableValues branch rest hbranches]
    simp only [hcondition, hstatus]
    exact ih variableValues rfl
  case case4 =>
    intro inherited caseCondition cursor possibleTypes environment branch rest
      hbranches literal hcondition hstatus ihFalse ihTrue variableValues
      henvironment
    subst environment
    rw [CaseCursor.BooleanEnvironment.concrete_statusForVariable] at hstatus
    cases hvalue : inputValueBoolean? variableValues (.variable literal.variableName) <;>
      simp [hvalue] at hstatus
  case case5 =>
    intro groups environment ih variableValues henvironment
    subst environment
    simp only [CaseCursor.summarizeFieldGroupsDecisionWithPruning.eq_1]
    apply BooleanDecision.combineMap_splitFree
    intro group hgroup
    exact BooleanDecision.map_splitFree (algebra.field group)
      (ih group hgroup variableValues rfl)
  case case6 =>
    intro group parentTypes environment ih variableValues henvironment
    subst environment
    simp only [CaseCursor.summarizeChildTypesDecisionWithPruning.eq_1]
    apply BooleanDecision.joinMap_splitFree
    intro childParentType hparentType
    exact ih childParentType variableValues rfl
  exact rfl

namespace CaseCursor

def summarize (algebra : Algebra) (schema : Schema)
    (inheritedBooleanCondition : List BooleanLiteral)
    (cursor : CaseCursor) (possibleTypes : PossibleTypeRegion)
    (variableValues : VariableValues)
    (fixedVariableValues : VariableValues := variableValues)
    : algebra.Summary :=
  (cursor.summarizeDecisionWithPruning algebra schema [] inheritedBooleanCondition []
    possibleTypes
    (CaseCursor.BooleanEnvironment.concrete variableValues) fixedVariableValues).collapse
    algebra

def summarizeChildTypes (algebra : Algebra) (schema : Schema)
    (group : CollectedFieldGroup) (parentTypes : TypeNames)
    (variableValues : VariableValues)
    (fixedVariableValues : VariableValues := variableValues)
    : algebra.Summary :=
  TreeSummary.joinMap algebra parentTypes
    fun childParentType _hparentType =>
      let childTree :=
        group.childTreeWithKnownFalsePruning schema childParentType fixedVariableValues
      summarize algebra schema group.childInheritedBooleanCondition
        (.ofConditionTree childTree) childTree.condition.possibleTypes variableValues
        fixedVariableValues

def summarizeFieldGroups (algebra : Algebra) (schema : Schema)
    (groups : List CollectedFieldGroup) (variableValues : VariableValues)
    (fixedVariableValues : VariableValues := variableValues)
    : algebra.Summary :=
  TreeSummary.combineMap algebra groups
    fun group _hgroup =>
      algebra.field group
        (summarizeChildTypes algebra schema group (childParentTypes schema group)
          variableValues fixedVariableValues)

theorem summarizeChildTypesDecisionWithPruning_collapse_complete
    (algebra : Algebra) (_lawful : algebra.Lawful) (schema : Schema)
    (group : CollectedFieldGroup) (parentTypes : TypeNames)
    (variableValues fixedVariableValues : VariableValues)
    : (CaseCursor.summarizeChildTypesDecisionWithPruning algebra schema [] group
        parentTypes (CaseCursor.BooleanEnvironment.concrete variableValues)
        fixedVariableValues).collapse
        algebra
      = summarizeChildTypes algebra schema group parentTypes variableValues
          fixedVariableValues := by
  simp only [CaseCursor.summarizeChildTypesDecisionWithPruning.eq_1]
  rw [BooleanDecision.collapse_joinMap]
  rfl

theorem summarizeChildTypesDecisionWithPruning_complete_splitFree
    (algebra : Algebra) (schema : Schema) (variableOrder : BooleanVariableNames)
    (group : CollectedFieldGroup) (parentTypes : TypeNames)
    (variableValues fixedVariableValues : VariableValues)
    : (CaseCursor.summarizeChildTypesDecisionWithPruning algebra schema variableOrder
        group parentTypes (CaseCursor.BooleanEnvironment.concrete variableValues)
        fixedVariableValues).SplitFree := by
  simp only [CaseCursor.summarizeChildTypesDecisionWithPruning.eq_1]
  apply BooleanDecision.joinMap_splitFree
  intro childParentType hparentType
  exact CaseCursor.summarizeDecisionWithPruning_complete_splitFree algebra schema variableOrder
    group.childInheritedBooleanCondition []
    (.ofConditionTree
      (group.childTreeWithKnownFalsePruning schema childParentType fixedVariableValues))
    (group.childTreeWithKnownFalsePruning schema childParentType
      fixedVariableValues).condition.possibleTypes
    variableValues fixedVariableValues

theorem summarizeDecisionWithPruning_complete_eq_of_booleanFree
    (algebra : Algebra) (schema : Schema) (variableOrder : BooleanVariableNames)
    (inheritedBooleanCondition caseCondition : List BooleanLiteral)
    (cursor : CaseCursor)
    (possibleTypes : PossibleTypeRegion) (left right fixedVariableValues : VariableValues)
    (hcursor : CaseCursorBooleanFree cursor)
    : cursor.summarizeDecisionWithPruning algebra schema variableOrder
        inheritedBooleanCondition caseCondition possibleTypes
        (CaseCursor.BooleanEnvironment.concrete left) fixedVariableValues
      = cursor.summarizeDecisionWithPruning algebra schema variableOrder
          inheritedBooleanCondition caseCondition possibleTypes
          (CaseCursor.BooleanEnvironment.concrete right) fixedVariableValues := by
  apply CaseCursor.summarizeDecisionWithPruning.induct schema fixedVariableValues
    (motive1 := fun inherited caseCondition cursor possibleTypes environment =>
      ∀ left right,
        environment = CaseCursor.BooleanEnvironment.concrete left
        -> CaseCursorBooleanFree cursor
        -> cursor.summarizeDecisionWithPruning algebra schema variableOrder inherited
              caseCondition possibleTypes environment
              fixedVariableValues
          = cursor.summarizeDecisionWithPruning algebra schema variableOrder inherited
              caseCondition possibleTypes
              (CaseCursor.BooleanEnvironment.concrete right) fixedVariableValues)
    (motive2 := fun groups environment =>
      ∀ left right,
        environment = CaseCursor.BooleanEnvironment.concrete left
        -> CollectedFieldGroupsBooleanFree groups
        -> CaseCursor.summarizeFieldGroupsDecisionWithPruning algebra schema variableOrder groups
              environment fixedVariableValues
          = CaseCursor.summarizeFieldGroupsDecisionWithPruning algebra schema variableOrder groups
              (CaseCursor.BooleanEnvironment.concrete right) fixedVariableValues)
    (motive3 := fun group parentTypes environment =>
      ∀ left right,
        environment = CaseCursor.BooleanEnvironment.concrete left
        -> SelectionConditions.selectionSetBooleanVariables group.mergedSelectionSet = []
        -> CaseCursor.summarizeChildTypesDecisionWithPruning algebra schema variableOrder group
              parentTypes environment fixedVariableValues
          = CaseCursor.summarizeChildTypesDecisionWithPruning algebra schema variableOrder group
              parentTypes (CaseCursor.BooleanEnvironment.concrete right) fixedVariableValues)
  case case1 =>
    intro inherited caseCondition cursor possibleTypes environment hbranches ih
      left right henvironment hcursor
    subst environment
    rw [CaseCursor.summarizeDecisionWithPruning_nil_values algebra schema variableOrder inherited
      caseCondition cursor possibleTypes
      (CaseCursor.BooleanEnvironment.concrete left) fixedVariableValues hbranches,
      CaseCursor.summarizeDecisionWithPruning_nil_values algebra schema variableOrder inherited
        caseCondition cursor possibleTypes
        (CaseCursor.BooleanEnvironment.concrete right) fixedVariableValues hbranches]
    exact ih left right rfl
      (cursor.fieldGroups_booleanFree hcursor _ possibleTypes)
  case case2 =>
    intro inherited caseCondition cursor possibleTypes environment branch rest
      hbranches typeName hcondition ihSelect ihSkip left right henvironment hcursor
    subst environment
    rw [CaseCursor.summarizeDecisionWithPruning_cons_values algebra schema variableOrder inherited
      caseCondition cursor possibleTypes
      (CaseCursor.BooleanEnvironment.concrete left) fixedVariableValues branch rest hbranches,
      CaseCursor.summarizeDecisionWithPruning_cons_values algebra schema variableOrder inherited
        caseCondition cursor possibleTypes
        (CaseCursor.BooleanEnvironment.concrete right) fixedVariableValues branch rest hbranches]
    simp only [hcondition]
    apply BooleanDecision.joinMap_congr algebra
    intro region hregion
    split
    · exact ihSelect region left right rfl
        (cursor.selectBranch_booleanFree hcursor hbranches ⟨typeName, hcondition⟩)
    · exact ihSkip region left right rfl
        (cursor.skipBranch_booleanFree hcursor hbranches)
  case case3 =>
    intro inherited caseCondition cursor possibleTypes environment branch rest
      hbranches literal hcondition value hstatus selectedLiteral ih left right
      henvironment hcursor
    exact (cursor.booleanBranch_impossible hcursor hbranches literal hcondition).elim
  case case4 =>
    intro inherited caseCondition cursor possibleTypes environment branch rest
      hbranches literal hcondition hstatus ihFalse ihTrue left right
      henvironment hcursor
    exact (cursor.booleanBranch_impossible hcursor hbranches literal hcondition).elim
  case case5 =>
    intro groups environment ih left right henvironment hgroups
    subst environment
    simp only [CaseCursor.summarizeFieldGroupsDecisionWithPruning.eq_1]
    apply BooleanDecision.combineMap_congr_orders algebra variableOrder variableOrder
    · intro group hgroup
      exact congrArg (BooleanDecision.map (algebra.field group))
        (ih group hgroup left right rfl (hgroups group hgroup))
    · intro group hgroup
      exact BooleanDecision.map_splitFree (algebra.field group)
        (summarizeChildTypesDecisionWithPruning_complete_splitFree algebra schema variableOrder group
          (childParentTypes schema group) right fixedVariableValues)
  case case6 =>
    intro group parentTypes environment ih left right henvironment hgroup
    subst environment
    simp only [CaseCursor.summarizeChildTypesDecisionWithPruning.eq_1]
    apply BooleanDecision.joinMap_congr algebra
    intro childParentType hparentType
    let tree := group.childTreeWithKnownFalsePruning schema childParentType
      fixedVariableValues
    have htree : conditionTreeBooleanVariables tree = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro variableName hvariable
      have hwithin :=
        ofSelectionSetInScopeWithKnownFalsePruning_booleanVariablesWithin schema
          childParentType group.childInheritedBooleanCondition fixedVariableValues
          group.mergedSelectionSet variableName hvariable
      rw [hgroup] at hwithin
      contradiction
    exact ih childParentType left right rfl
      (CaseCursor.ofConditionTree_booleanFree tree htree)
  exact rfl
  exact hcursor

theorem summarizeFieldGroups_le_decision_complete
    (algebra : Algebra) {lawful : algebra.Lawful}
    (joinFactoringLaws : ExactCases.JoinFactoringLaws algebra lawful)
    (schema : Schema) (groups : List CollectedFieldGroup)
    (variableValues fixedVariableValues : VariableValues)
    : lawful.le
        (summarizeFieldGroups algebra schema groups variableValues fixedVariableValues)
        ((CaseCursor.summarizeFieldGroupsDecisionWithPruning algebra schema [] groups
            (CaseCursor.BooleanEnvironment.concrete variableValues)
            fixedVariableValues).collapse
          algebra) := by
  simp only [CaseCursor.summarizeFieldGroupsDecisionWithPruning.eq_1]
  unfold summarizeFieldGroups
  apply lawful.le_trans _
    (TreeSummary.combineMap algebra groups fun group hgroup =>
      (((CaseCursor.summarizeChildTypesDecisionWithPruning algebra schema [] group
        (childParentTypes schema group)
        (CaseCursor.BooleanEnvironment.concrete variableValues) fixedVariableValues).map
          (algebra.field group)).collapse algebra))
  · apply BooleanDecision.combineMap_mono algebra lawful
    intro group hgroup
    rw [← summarizeChildTypesDecisionWithPruning_collapse_complete algebra lawful schema group
      (childParentTypes schema group) variableValues fixedVariableValues]
    exact BooleanDecision.collapse_map_le_of_splitFree algebra lawful joinFactoringLaws.join_le
      (algebra.field group) (joinFactoringLaws.field_join_le group)
      (summarizeChildTypesDecisionWithPruning_complete_splitFree algebra schema [] group
        (childParentTypes schema group) variableValues fixedVariableValues)
  · apply BooleanDecision.collapse_combineMap_le_of_splitFree algebra lawful
      joinFactoringLaws.join_le joinFactoringLaws.combine_join_le
    intro group hgroup
    exact BooleanDecision.map_splitFree (algebra.field group)
      (summarizeChildTypesDecisionWithPruning_complete_splitFree algebra schema [] group
        (childParentTypes schema group) variableValues fixedVariableValues)

theorem summarizeDecisionWithPruning_complete_order_independent
    (algebra : Algebra) (schema : Schema)
    (leftOrder rightOrder : BooleanVariableNames)
    (inheritedBooleanCondition caseCondition : List BooleanLiteral)
    (cursor : CaseCursor)
    (possibleTypes : PossibleTypeRegion)
    (variableValues fixedVariableValues : VariableValues)
    : CaseCursor.summarizeDecisionWithPruning algebra schema leftOrder
        inheritedBooleanCondition caseCondition cursor possibleTypes
        (CaseCursor.BooleanEnvironment.concrete variableValues) fixedVariableValues
      = CaseCursor.summarizeDecisionWithPruning algebra schema rightOrder
          inheritedBooleanCondition caseCondition cursor possibleTypes
          (CaseCursor.BooleanEnvironment.concrete variableValues)
          fixedVariableValues := by
  apply CaseCursor.summarizeDecisionWithPruning.induct schema fixedVariableValues
    (motive1 := fun inherited caseCondition cursor possibleTypes environment =>
      ∀ variableValues,
        environment = CaseCursor.BooleanEnvironment.concrete variableValues
        -> ∀ leftOrder rightOrder,
          CaseCursor.summarizeDecisionWithPruning algebra schema leftOrder inherited
              caseCondition cursor possibleTypes environment fixedVariableValues
            = CaseCursor.summarizeDecisionWithPruning algebra schema rightOrder inherited
                caseCondition cursor possibleTypes environment fixedVariableValues)
    (motive2 := fun groups environment =>
      ∀ variableValues,
        environment = CaseCursor.BooleanEnvironment.concrete variableValues
        -> ∀ leftOrder rightOrder,
          CaseCursor.summarizeFieldGroupsDecisionWithPruning algebra schema leftOrder groups environment
              fixedVariableValues
            = CaseCursor.summarizeFieldGroupsDecisionWithPruning algebra schema rightOrder groups
                environment fixedVariableValues)
    (motive3 := fun group parentTypes environment =>
      ∀ variableValues,
        environment = CaseCursor.BooleanEnvironment.concrete variableValues
        -> ∀ leftOrder rightOrder,
          CaseCursor.summarizeChildTypesDecisionWithPruning algebra schema leftOrder group parentTypes
              environment fixedVariableValues
            = CaseCursor.summarizeChildTypesDecisionWithPruning algebra schema rightOrder group
                parentTypes environment fixedVariableValues)
  case case1 =>
    intro inherited caseCondition cursor possibleTypes environment
      hbranches ih variableValues henvironment leftOrder rightOrder
    subst environment
    rw [CaseCursor.summarizeDecisionWithPruning_nil_values algebra schema leftOrder inherited
      caseCondition cursor possibleTypes
      (CaseCursor.BooleanEnvironment.concrete variableValues) fixedVariableValues hbranches,
      CaseCursor.summarizeDecisionWithPruning_nil_values algebra schema rightOrder inherited
        caseCondition cursor possibleTypes
        (CaseCursor.BooleanEnvironment.concrete variableValues) fixedVariableValues hbranches]
    exact ih variableValues rfl leftOrder rightOrder
  case case2 =>
    intro inherited caseCondition cursor possibleTypes environment branch rest
      hbranches typeName hcondition ihSelect ihSkip variableValues henvironment leftOrder
      rightOrder
    subst environment
    rw [CaseCursor.summarizeDecisionWithPruning_cons_values algebra schema leftOrder inherited
      caseCondition cursor possibleTypes
      (CaseCursor.BooleanEnvironment.concrete variableValues) fixedVariableValues branch rest hbranches,
      CaseCursor.summarizeDecisionWithPruning_cons_values algebra schema rightOrder inherited
        caseCondition cursor possibleTypes
        (CaseCursor.BooleanEnvironment.concrete variableValues) fixedVariableValues branch rest hbranches]
    simp only [hcondition]
    apply BooleanDecision.joinMap_congr algebra
    intro region hregion
    split
    · exact ihSelect region variableValues rfl leftOrder rightOrder
    · exact ihSkip region variableValues rfl leftOrder rightOrder
  case case3 =>
    intro inherited caseCondition cursor possibleTypes environment branch rest
      hbranches literal hcondition value hstatus selectedLiteral ih variableValues
      henvironment leftOrder rightOrder
    subst environment
    rw [CaseCursor.summarizeDecisionWithPruning_cons_values algebra schema leftOrder inherited
      caseCondition cursor possibleTypes
      (CaseCursor.BooleanEnvironment.concrete variableValues) fixedVariableValues branch rest hbranches,
      CaseCursor.summarizeDecisionWithPruning_cons_values algebra schema rightOrder inherited
        caseCondition cursor possibleTypes
        (CaseCursor.BooleanEnvironment.concrete variableValues) fixedVariableValues branch rest hbranches]
    simp only [hcondition, hstatus]
    exact ih variableValues rfl leftOrder rightOrder
  case case4 =>
    intro inherited caseCondition cursor possibleTypes environment branch rest
      hbranches literal hcondition hstatus ihFalse ihTrue variableValues
      henvironment leftOrder rightOrder
    subst environment
    rw [CaseCursor.BooleanEnvironment.concrete_statusForVariable] at hstatus
    cases hvalue : inputValueBoolean? variableValues (.variable literal.variableName) <;>
      simp [hvalue] at hstatus
  case case5 =>
    intro groups environment ih variableValues henvironment
      leftOrder rightOrder
    subst environment
    simp only [CaseCursor.summarizeFieldGroupsDecisionWithPruning.eq_1]
    apply BooleanDecision.combineMap_congr_orders algebra leftOrder rightOrder
    · intro group hgroup
      exact congrArg (BooleanDecision.map (algebra.field group))
        (ih group hgroup variableValues rfl leftOrder rightOrder)
    · intro group hgroup
      exact BooleanDecision.map_splitFree (algebra.field group)
        (summarizeChildTypesDecisionWithPruning_complete_splitFree algebra schema rightOrder group
          (childParentTypes schema group) variableValues fixedVariableValues)
  case case6 =>
    intro group parentTypes environment ih variableValues henvironment leftOrder rightOrder
    subst environment
    simp only [CaseCursor.summarizeChildTypesDecisionWithPruning.eq_1]
    apply BooleanDecision.joinMap_congr algebra
    intro childParentType hparentType
    exact ih childParentType variableValues rfl leftOrder rightOrder
  exact rfl

end CaseCursor

theorem CaseCursor.summarize_ofConditionTree_eq_resolved
    (algebra : Algebra) (schema : Schema)
    (inheritedBooleanCondition : List BooleanLiteral)
    (tree : Tree) (variableValues fixedVariableValues : VariableValues)
    : CaseCursor.summarize algebra schema inheritedBooleanCondition
        (.ofConditionTree tree) tree.condition.possibleTypes variableValues
        fixedVariableValues
      = summarizeConditionTreeResolved algebra schema inheritedBooleanCondition tree
          variableValues fixedVariableValues := by
  unfold CaseCursor.summarize summarizeConditionTreeResolved
    summarizeConditionTreeWithPruning summarizeConditionTreeDecisionWithPruning
  rw [BooleanDecision.collapse_compact]
  exact congrArg (BooleanDecision.collapse algebra)
    (CaseCursor.summarizeDecisionWithPruning_complete_order_independent algebra schema []
      (conditionTreeBooleanVariables tree).eraseDups inheritedBooleanCondition []
      (.ofConditionTree tree) tree.condition.possibleTypes
      variableValues fixedVariableValues)

private theorem summarizeConditionTreeResolved_le_environment
    (algebra : Algebra) {lawful : algebra.Lawful}
    (joinFactoringLaws : ExactCases.JoinFactoringLaws algebra lawful) (schema : Schema)
    (inheritedBooleanCondition : List BooleanLiteral)
    (tree : Tree) (environment : CaseCursor.BooleanEnvironment)
    (variableValues fixedVariableValues : VariableValues)
    (hrealizes : environment.Realizes variableValues)
    (hsymbolic : environment.IsSymbolic)
    : lawful.le
        (summarizeConditionTreeResolved algebra schema inheritedBooleanCondition tree
          variableValues fixedVariableValues)
        (summarizeConditionTreeWithPruning algebra schema inheritedBooleanCondition tree
          environment fixedVariableValues) := by
  unfold summarizeConditionTreeResolved summarizeConditionTreeWithPruning
    summarizeConditionTreeDecisionWithPruning
  rw [BooleanDecision.collapse_compact, BooleanDecision.collapse_compact]
  apply BooleanDecision.Refines.collapse_le algebra lawful joinFactoringLaws.join_le variableValues
  exact CaseCursor.summarizeDecisionWithPruning_refines_complete algebra schema
    (conditionTreeBooleanVariables tree).eraseDups inheritedBooleanCondition []
    (.ofConditionTree tree) tree.condition.possibleTypes environment variableValues
    fixedVariableValues hrealizes hsymbolic

theorem summarizeOperationResolved_le_unknown
    (algebra : Algebra) {lawful : algebra.Lawful}
    (joinFactoringLaws : ExactCases.JoinFactoringLaws algebra lawful) (schema : Schema)
    (operation : Operation) (variableValues : VariableValues)
    : lawful.le
        (summarizeSelectionSetResolved algebra schema (operation.rootType schema) []
          operation.selectionSet variableValues [])
        (summarizeOperation algebra schema operation) := by
  unfold summarizeSelectionSetResolved summarizeOperation
  apply summarizeConditionTreeResolved_le_environment algebra joinFactoringLaws schema
    [] _ CaseCursor.BooleanEnvironment.unresolved variableValues []
  · exact CaseCursor.BooleanEnvironment.unresolved_realizes variableValues
  · trivial

end ExactCases
end TreeSummary
end GraphQL
