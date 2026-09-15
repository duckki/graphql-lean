import Proofs.GraphQL.Theories.TreeSummary.ExactCases.BooleanDecision
import Proofs.GraphQL.Theories.TreeSummary.Algebra

/-! Algebra relations lifted through the incremental exact-case cursor. -/

namespace GraphQL
namespace TreeSummary
namespace ExactCases

universe u v

open GraphQL.ConditionTree
open Internal

namespace Internal.BooleanDecision

inductive Related (relation : α -> β -> Prop)
    : BooleanDecision α -> BooleanDecision β -> Prop
  | leaf {left right} (hrelated : relation left right)
    : Related relation (.leaf left) (.leaf right)
  | split {test leftFalse leftTrue rightFalse rightTrue}
    (hfalse : Related relation leftFalse rightFalse)
    (htrue : Related relation leftTrue rightTrue)
    : Related relation (.split test leftFalse leftTrue) (.split test rightFalse rightTrue)
  | join {leftFirst leftSecond rightFirst rightSecond}
    (hfirst : Related relation leftFirst rightFirst)
    (hsecond : Related relation leftSecond rightSecond)
    : Related relation (.join leftFirst leftSecond) (.join rightFirst rightSecond)

theorem Related.map
    (transformLeft : α -> γ) (transformRight : β -> δ)
    (htransform
      : ∀ left right,
          relation left right
          -> resultRelation (transformLeft left) (transformRight right))
    {left : BooleanDecision α} {right : BooleanDecision β}
    (hrelated : Related relation left right)
    : Related resultRelation (left.map transformLeft) (right.map transformRight) := by
  induction hrelated with
  | leaf h => exact .leaf (htransform _ _ h)
  | split _ _ ihFalse ihTrue => exact .split ihFalse ihTrue
  | join _ _ ihFirst ihSecond => exact .join ihFirst ihSecond

theorem Related.restrict (selectedVariable : Name) (selectedValue : Bool)
    {left : BooleanDecision α} {right : BooleanDecision β}
    (hrelated : Related relation left right)
    : Related relation (left.restrict selectedVariable selectedValue)
        (right.restrict selectedVariable selectedValue) := by
  induction hrelated with
  | leaf h => exact .leaf h
  | split hfalse htrue ihFalse ihTrue =>
      simp only [BooleanDecision.restrict]
      split
      · cases selectedValue <;> assumption
      · exact .split ihFalse ihTrue
  | join _ _ ihFirst ihSecond => exact .join ihFirst ihSecond

private def decisionNodeCount : BooleanDecision α -> Nat
  | .leaf _summary => 1
  | .split _variableName onFalse onTrue =>
      1 + decisionNodeCount onFalse + decisionNodeCount onTrue
  | .join left right => 1 + decisionNodeCount left + decisionNodeCount right

private theorem decisionNodeCount_restrict_le (selectedVariable : Name)
    (selectedValue : Bool) (decision : BooleanDecision α)
    : decisionNodeCount (decision.restrict selectedVariable selectedValue)
      ≤ decisionNodeCount decision := by
  induction decision with
  | leaf => simp [BooleanDecision.restrict, decisionNodeCount]
  | split test onFalse onTrue ihFalse ihTrue =>
      simp only [BooleanDecision.restrict]
      split
      · cases selectedValue <;> simp_all [decisionNodeCount] <;> omega
      · simp only [decisionNodeCount]
        omega
  | join left right ihLeft ihRight =>
      simp only [BooleanDecision.restrict, decisionNodeCount]
      omega

theorem Related.zipWith
    (variableOrder : BooleanVariableNames)
    (leftOperation : α -> γ -> ε) (rightOperation : β -> δ -> ζ)
    (hoperation
      : ∀ left right otherLeft otherRight,
          relation left right
          -> otherRelation otherLeft otherRight
          -> resultRelation (leftOperation left otherLeft)
              (rightOperation right otherRight))
    {left : BooleanDecision α} {right : BooleanDecision β}
    {otherLeft : BooleanDecision γ} {otherRight : BooleanDecision δ}
    (hleft : Related relation left right)
    (hright : Related otherRelation otherLeft otherRight)
    : Related resultRelation
        (BooleanDecision.zipWith variableOrder leftOperation left otherLeft)
        (BooleanDecision.zipWith variableOrder rightOperation right otherRight) := by
  cases hleft with
  | leaf hvalue =>
      simp only [BooleanDecision.zipWith]
      exact hright.map _ _ (fun l r h => hoperation _ _ _ _ hvalue h)
  | @split test leftFalse leftTrue rightFalse rightTrue hfalse htrue =>
      cases hright with
      | leaf hvalue =>
          simp only [BooleanDecision.zipWith]
          exact (Related.split hfalse htrue).map _ _
            (fun l r h => hoperation _ _ _ _ h hvalue)
      | @split otherTest otherLeftFalse otherLeftTrue otherRightFalse
          otherRightTrue hotherFalse hotherTrue =>
          simp only [BooleanDecision.zipWith]
          split
          · exact .split
              (Related.zipWith variableOrder leftOperation rightOperation hoperation
                hfalse hotherFalse)
              (Related.zipWith variableOrder leftOperation rightOperation hoperation
                htrue hotherTrue)
          · split
            · exact .split
                (Related.zipWith variableOrder leftOperation rightOperation hoperation
                  hfalse
                  ((Related.split hotherFalse hotherTrue).restrict test false))
                (Related.zipWith variableOrder leftOperation rightOperation hoperation
                  htrue
                  ((Related.split hotherFalse hotherTrue).restrict test true))
            · exact .split
                (Related.zipWith variableOrder leftOperation rightOperation hoperation
                  ((Related.split hfalse htrue).restrict otherTest false)
                  hotherFalse)
                (Related.zipWith variableOrder leftOperation rightOperation hoperation
                  ((Related.split hfalse htrue).restrict otherTest true)
                  hotherTrue)
      | @join otherLeftFirst otherLeftSecond otherRightFirst otherRightSecond
          hfirst hsecond =>
          simp only [BooleanDecision.zipWith]
          exact .join
            (Related.zipWith variableOrder leftOperation rightOperation hoperation
              (.split hfalse htrue) hfirst)
            (Related.zipWith variableOrder leftOperation rightOperation hoperation
              (.split hfalse htrue) hsecond)
  | @join leftFirst leftSecond rightFirst rightSecond hfirst hsecond =>
      cases hright with
      | leaf hvalue =>
          simp only [BooleanDecision.zipWith]
          exact (Related.join hfirst hsecond).map _ _
            (fun l r h => hoperation _ _ _ _ h hvalue)
      | split hotherFalse hotherTrue =>
          simp only [BooleanDecision.zipWith]
          exact .join
            (Related.zipWith variableOrder leftOperation rightOperation hoperation
              hfirst (.split hotherFalse hotherTrue))
            (Related.zipWith variableOrder leftOperation rightOperation hoperation
              hsecond (.split hotherFalse hotherTrue))
      | join hotherFirst hotherSecond =>
          simp only [BooleanDecision.zipWith]
          exact .join
            (Related.zipWith variableOrder leftOperation rightOperation hoperation
              hfirst (.join hotherFirst hotherSecond))
            (Related.zipWith variableOrder leftOperation rightOperation hoperation
              hsecond (.join hotherFirst hotherSecond))
termination_by decisionNodeCount left + decisionNodeCount otherLeft
decreasing_by
  all_goals simp only [decisionNodeCount]
  all_goals try omega
  all_goals
    have hotherFalse := decisionNodeCount_restrict_le test false
      (.split otherTest otherLeftFalse otherLeftTrue)
    have hotherTrue := decisionNodeCount_restrict_le test true
      (.split otherTest otherLeftFalse otherLeftTrue)
    have hleftFalse := decisionNodeCount_restrict_le otherTest false
      (.split test leftFalse leftTrue)
    have hleftTrue := decisionNodeCount_restrict_le otherTest true
      (.split test leftFalse leftTrue)
    simp only [decisionNodeCount] at hotherFalse hotherTrue hleftFalse hleftTrue
    omega

theorem Related.collapse (leftAlgebra : Algebra.{u}) (rightAlgebra : Algebra.{v})
    (algebraRelation : leftAlgebra.Relation rightAlgebra)
    {left : BooleanDecision leftAlgebra.Summary}
    {right : BooleanDecision rightAlgebra.Summary}
    (hrelated : Related algebraRelation.related left right)
    : algebraRelation.related (left.collapse leftAlgebra)
        (right.collapse rightAlgebra) := by
  induction hrelated with
  | leaf h => exact h
  | split _ _ ihFalse ihTrue => exact algebraRelation.join_related _ _ _ _ ihFalse ihTrue
  | join _ _ ihFirst ihSecond =>
      exact algebraRelation.join_related _ _ _ _ ihFirst ihSecond

theorem Related.combineMap (leftAlgebra : Algebra.{u}) (rightAlgebra : Algebra.{v})
    (algebraRelation : leftAlgebra.Relation rightAlgebra)
    (variableOrder : BooleanVariableNames) (items : List α)
    (left : ∀ item, item ∈ items -> BooleanDecision leftAlgebra.Summary)
    (right : ∀ item, item ∈ items -> BooleanDecision rightAlgebra.Summary)
    (hitems
      : ∀ item hitem,
          Related algebraRelation.related (left item hitem) (right item hitem))
    : Related algebraRelation.related
        (BooleanDecision.combineMap leftAlgebra variableOrder items left)
        (BooleanDecision.combineMap rightAlgebra variableOrder items right) := by
  induction items with
  | nil =>
      simpa [BooleanDecision.combineMap]
        using (Related.leaf algebraRelation.empty_related)
  | cons item rest ih =>
      rw [BooleanDecision.combineMap, BooleanDecision.combineMap]
      apply Related.zipWith variableOrder leftAlgebra.combine rightAlgebra.combine
      · exact fun _ _ _ _ => algebraRelation.combine_related _ _ _ _
      · exact hitems item (by simp)
      · exact ih
          (fun candidate hcandidate => left candidate (by simp [hcandidate]))
          (fun candidate hcandidate => right candidate (by simp [hcandidate]))
          (fun candidate hcandidate => hitems candidate (by simp [hcandidate]))

theorem Related.joinMap (leftAlgebra : Algebra.{u}) (rightAlgebra : Algebra.{v})
    (algebraRelation : leftAlgebra.Relation rightAlgebra)
    (items : List α)
    (left : ∀ item, item ∈ items -> BooleanDecision leftAlgebra.Summary)
    (right : ∀ item, item ∈ items -> BooleanDecision rightAlgebra.Summary)
    (hitems
      : ∀ item hitem,
          Related algebraRelation.related (left item hitem) (right item hitem))
    : Related algebraRelation.related
        (BooleanDecision.joinMap leftAlgebra items left)
        (BooleanDecision.joinMap rightAlgebra items right) := by
  cases items with
  | nil =>
      simpa [BooleanDecision.joinMap] using (Related.leaf algebraRelation.empty_related)
  | cons item rest =>
      cases rest with
      | nil => simpa [BooleanDecision.joinMap] using hitems item (by simp)
      | cons next tail =>
          rw [BooleanDecision.joinMap, BooleanDecision.joinMap]
          exact .join
            (hitems item (by simp))
            (Related.joinMap leftAlgebra rightAlgebra algebraRelation (next :: tail)
              (fun candidate hcandidate => left candidate (by simp [hcandidate]))
              (fun candidate hcandidate => right candidate (by simp [hcandidate]))
              (fun candidate hcandidate => hitems candidate (by simp [hcandidate])))
termination_by items.length

end BooleanDecision
end Internal

private theorem CaseCursor.summarizeDecisionWithPruning_nil
    (algebra : Algebra) (schema : Schema) (variableOrder : BooleanVariableNames)
    (inheritedBooleanCondition caseCondition : List BooleanLiteral)
    (cursor : CaseCursor)
    (possibleTypes : PossibleTypeRegion) (environment : CaseCursor.BooleanEnvironment)
    (pruningValues : Execution.VariableValues := environment.pruningValues)
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

private theorem CaseCursor.summarizeDecisionWithPruning_cons
    (algebra : Algebra) (schema : Schema) (variableOrder : BooleanVariableNames)
    (inheritedBooleanCondition caseCondition : List BooleanLiteral)
    (cursor : CaseCursor)
    (possibleTypes : PossibleTypeRegion) (environment : CaseCursor.BooleanEnvironment)
    (pruningValues : Execution.VariableValues := environment.pruningValues)
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

theorem CaseCursor.summarizeDecisionWithPruning_related
    (left : Algebra.{u}) (right : Algebra.{v})
    (algebraRelation : left.Relation right) (schema : Schema)
    (variableOrder : BooleanVariableNames)
    (inheritedBooleanCondition caseCondition : List BooleanLiteral)
    (cursor : CaseCursor)
    (possibleTypes : PossibleTypeRegion) (environment : CaseCursor.BooleanEnvironment)
    (pruningValues : Execution.VariableValues := environment.pruningValues)
    : BooleanDecision.Related algebraRelation.related
        (CaseCursor.summarizeDecisionWithPruning left schema variableOrder
          inheritedBooleanCondition caseCondition cursor possibleTypes environment
          pruningValues)
        (CaseCursor.summarizeDecisionWithPruning right schema variableOrder
          inheritedBooleanCondition caseCondition cursor possibleTypes environment
          pruningValues) := by
  apply CaseCursor.summarizeDecisionWithPruning.induct schema pruningValues
    (motive1 :=
      fun inherited caseCondition cursor possibleTypes environment =>
        BooleanDecision.Related algebraRelation.related
          (CaseCursor.summarizeDecisionWithPruning left schema variableOrder inherited
            caseCondition cursor possibleTypes environment pruningValues)
          (CaseCursor.summarizeDecisionWithPruning right schema variableOrder inherited
            caseCondition cursor possibleTypes environment pruningValues))
    (motive2 :=
      fun groups environment =>
        BooleanDecision.Related algebraRelation.related
          (CaseCursor.summarizeFieldGroupsDecisionWithPruning left schema variableOrder
            groups environment pruningValues)
          (CaseCursor.summarizeFieldGroupsDecisionWithPruning right schema variableOrder
            groups environment pruningValues))
    (motive3 :=
      fun group parentTypes environment =>
        BooleanDecision.Related algebraRelation.related
          (CaseCursor.summarizeChildTypesDecisionWithPruning left schema variableOrder
            group parentTypes environment pruningValues)
          (CaseCursor.summarizeChildTypesDecisionWithPruning right schema variableOrder
            group parentTypes environment pruningValues))
  case case1 =>
    intro inherited caseCondition cursor possibleTypes environment
      hbranches ih
    rw [CaseCursor.summarizeDecisionWithPruning_nil left schema variableOrder inherited
      caseCondition cursor possibleTypes environment pruningValues hbranches,
      CaseCursor.summarizeDecisionWithPruning_nil right schema variableOrder inherited
        caseCondition cursor possibleTypes environment pruningValues hbranches]
    exact ih
  case case2 =>
    intro inherited caseCondition cursor possibleTypes environment
      branch rest hbranches typeName hcondition ihSelect ihSkip
    rw [CaseCursor.summarizeDecisionWithPruning_cons left schema variableOrder inherited
      caseCondition cursor possibleTypes environment pruningValues branch rest
      hbranches,
      CaseCursor.summarizeDecisionWithPruning_cons right schema variableOrder inherited
        caseCondition cursor possibleTypes environment pruningValues branch rest
        hbranches]
    simp only [hcondition]
    apply BooleanDecision.Related.joinMap left right algebraRelation
    intro region hregion
    split
    · exact ihSelect region
    · exact ihSkip region
  case case3 =>
    intro inherited caseCondition cursor possibleTypes environment
      branch rest hbranches literal hcondition value hstatus selectedLiteral ih
    rw [CaseCursor.summarizeDecisionWithPruning_cons left schema variableOrder inherited
      caseCondition cursor possibleTypes environment pruningValues branch rest
      hbranches,
      CaseCursor.summarizeDecisionWithPruning_cons right schema variableOrder inherited
        caseCondition cursor possibleTypes environment pruningValues branch rest
        hbranches]
    simp only [hcondition, hstatus]
    exact ih
  case case4 =>
    intro inherited caseCondition cursor possibleTypes environment
      branch rest hbranches literal hcondition hstatus ihFalse ihTrue
    rw [CaseCursor.summarizeDecisionWithPruning_cons left schema variableOrder inherited
      caseCondition cursor possibleTypes environment pruningValues branch rest
      hbranches,
      CaseCursor.summarizeDecisionWithPruning_cons right schema variableOrder inherited
        caseCondition cursor possibleTypes environment pruningValues branch rest
        hbranches]
    simp only [hcondition, hstatus]
    exact BooleanDecision.Related.split ihFalse ihTrue
  case case5 =>
    intro groups environment ih
    simp only [CaseCursor.summarizeFieldGroupsDecisionWithPruning.eq_1]
    apply BooleanDecision.Related.combineMap left right algebraRelation variableOrder
    intro group hgroup
    apply BooleanDecision.Related.map _ _
    · intro leftChildren rightChildren hchildren
      exact algebraRelation.field_related group _ _ hchildren
    · exact ih group hgroup
  case case6 =>
    intro group parentTypes environment ih
    simp only [CaseCursor.summarizeChildTypesDecisionWithPruning.eq_1]
    apply BooleanDecision.Related.joinMap left right algebraRelation
    intro childParentType hparentType
    exact ih childParentType

theorem CaseCursor.summarizeChildTypesDecisionWithPruning_related
    (left : Algebra.{u}) (right : Algebra.{v})
    (algebraRelation : left.Relation right) (schema : Schema)
    (variableOrder : BooleanVariableNames)
    (group : CollectedFieldGroup) (parentTypes : TypeNames)
    (environment : CaseCursor.BooleanEnvironment)
    (pruningValues : Execution.VariableValues := environment.pruningValues)
    : BooleanDecision.Related algebraRelation.related
        (CaseCursor.summarizeChildTypesDecisionWithPruning left schema variableOrder group
          parentTypes environment pruningValues)
        (CaseCursor.summarizeChildTypesDecisionWithPruning right schema variableOrder
          group parentTypes environment pruningValues) := by
  simp only [CaseCursor.summarizeChildTypesDecisionWithPruning.eq_1]
  apply BooleanDecision.Related.joinMap left right algebraRelation
  intro childParentType hparentType
  exact CaseCursor.summarizeDecisionWithPruning_related left right algebraRelation schema
    variableOrder group.childInheritedBooleanCondition []
    (.ofConditionTree
      (group.childTreeWithKnownFalsePruning schema childParentType
        pruningValues))
    (group.childTreeWithKnownFalsePruning schema childParentType
      pruningValues).condition.possibleTypes environment pruningValues

theorem CaseCursor.summarizeFieldGroupsDecisionWithPruning_related
    (left : Algebra.{u}) (right : Algebra.{v})
    (algebraRelation : left.Relation right) (schema : Schema)
    (variableOrder : BooleanVariableNames)
    (groups : List CollectedFieldGroup) (environment : CaseCursor.BooleanEnvironment)
    (pruningValues : Execution.VariableValues := environment.pruningValues)
    : BooleanDecision.Related algebraRelation.related
        (CaseCursor.summarizeFieldGroupsDecisionWithPruning left schema variableOrder
          groups environment pruningValues)
        (CaseCursor.summarizeFieldGroupsDecisionWithPruning right schema variableOrder
          groups environment pruningValues) := by
  simp only [CaseCursor.summarizeFieldGroupsDecisionWithPruning.eq_1]
  apply BooleanDecision.Related.combineMap left right algebraRelation variableOrder
  intro group hgroup
  apply BooleanDecision.Related.map _ _
  · intro leftChildren rightChildren hchildren
    exact algebraRelation.field_related group _ _ hchildren
  · exact CaseCursor.summarizeChildTypesDecisionWithPruning_related left right algebraRelation
      schema variableOrder group (childParentTypes schema group) environment
      pruningValues

theorem CaseForest.summarize_related
    (left : Algebra.{u}) (right : Algebra.{v})
    (algebraRelation : left.Relation right) (schema : Schema)
    (inheritedBooleanCondition : List BooleanLiteral)
    (forest : CaseForest) (possibleTypes : PossibleTypeRegion)
    (variableValues fixedVariableValues : Execution.VariableValues)
    : algebraRelation.related
        (CaseForest.summarize left schema inheritedBooleanCondition forest
          possibleTypes variableValues fixedVariableValues)
        (CaseForest.summarize right schema inheritedBooleanCondition forest
          possibleTypes variableValues fixedVariableValues) := by
  apply CaseForest.summarize.induct schema variableValues fixedVariableValues
    (motive1 := fun inherited forest possibleTypes =>
      algebraRelation.related
        (CaseForest.summarize left schema inherited forest possibleTypes
          variableValues fixedVariableValues)
        (CaseForest.summarize right schema inherited forest possibleTypes
          variableValues fixedVariableValues))
    (motive2 := fun groups =>
      algebraRelation.related
        (CaseForest.summarizeFieldGroups left schema groups variableValues
          fixedVariableValues)
        (CaseForest.summarizeFieldGroups right schema groups variableValues
          fixedVariableValues))
    (motive3 := fun group parentTypes =>
      algebraRelation.related
        (CaseForest.summarizeChildTypes left schema group parentTypes
          variableValues fixedVariableValues)
        (CaseForest.summarizeChildTypes right schema group parentTypes
          variableValues fixedVariableValues))
    (motive4 := fun inherited forest regions hbranches =>
      algebraRelation.related
        (CaseForest.summarizeTypeRegions left schema inherited forest regions
          variableValues hbranches fixedVariableValues)
        (CaseForest.summarizeTypeRegions right schema inherited forest regions
          variableValues hbranches fixedVariableValues))
  case case1 =>
    intro inherited forest possibleTypes hbranches htypes ih
    rw [CaseForest.summarize.eq_1 right schema inherited forest possibleTypes
      variableValues fixedVariableValues]
    rw [CaseForest.summarize.eq_1 left schema inherited forest possibleTypes
      variableValues fixedVariableValues]
    simpa [hbranches, htypes] using ih
  case case2 =>
    intro inherited forest possibleTypes hbranches htypes ih
    rw [CaseForest.summarize.eq_1 right schema inherited forest possibleTypes
      variableValues fixedVariableValues]
    rw [CaseForest.summarize.eq_1 left schema inherited forest possibleTypes
      variableValues fixedVariableValues]
    simpa [hbranches, htypes] using ih
  case case3 =>
    intro inherited forest possibleTypes hbranches ih
    rw [CaseForest.summarize.eq_1 right schema inherited forest possibleTypes
      variableValues fixedVariableValues]
    rw [CaseForest.summarize.eq_1 left schema inherited forest possibleTypes
      variableValues fixedVariableValues]
    simpa [hbranches] using ih
  case case4 =>
    intro groups ih
    simp only [CaseForest.summarizeFieldGroups.eq_1]
    apply algebraRelation.combineMap_related groups
    intro group hgroup
    exact algebraRelation.field_related group _ _ (ih group hgroup)
  case case5 =>
    intro group parentTypes ih
    simp only [CaseForest.summarizeChildTypes.eq_1]
    apply algebraRelation.joinMap_related parentTypes
    intro childParentType hparentType
    exact ih childParentType
  case case6 =>
    intro inherited forest regions hbranches ih
    simp only [CaseForest.summarizeTypeRegions.eq_1]
    apply algebraRelation.joinMap_related regions
    intro region hregion
    exact ih region

theorem CaseCursor.summarizeConditionTree_related
    (left : Algebra.{u}) (right : Algebra.{v})
    (algebraRelation : left.Relation right) (schema : Schema)
    (inheritedBooleanCondition : List BooleanLiteral)
    (tree : Tree) (caseValues : Execution.VariableValues)
    : algebraRelation.related
        (CaseCursor.summarizeConditionTree left schema inheritedBooleanCondition tree
          caseValues)
        (CaseCursor.summarizeConditionTree right schema inheritedBooleanCondition tree
          caseValues) := by
  unfold CaseCursor.summarizeConditionTree Internal.summarizeConditionTreeDecision
  rw [BooleanDecision.collapse_compact, BooleanDecision.collapse_compact]
  apply BooleanDecision.Related.collapse left right algebraRelation
  exact CaseCursor.summarizeDecisionWithPruning_related left right algebraRelation schema
    (conditionTreeBooleanVariables tree).eraseDups inheritedBooleanCondition
    [] (.ofConditionTree tree) tree.condition.possibleTypes (.symbolic caseValues) []

theorem CaseForest.summarizeConditionTree_related
    (left : Algebra.{u}) (right : Algebra.{v})
    (algebraRelation : left.Relation right) (schema : Schema)
    (inheritedBooleanCondition : List BooleanLiteral)
    (tree : Tree) (variableValues fixedVariableValues : Execution.VariableValues)
    : algebraRelation.related
        (CaseForest.summarizeConditionTree left schema inheritedBooleanCondition tree
          variableValues fixedVariableValues)
        (CaseForest.summarizeConditionTree right schema inheritedBooleanCondition tree
          variableValues fixedVariableValues) := by
  exact CaseForest.summarize_related left right algebraRelation schema
    inheritedBooleanCondition (.ofConditionTree tree) tree.condition.possibleTypes
    variableValues fixedVariableValues

end ExactCases
end TreeSummary
end GraphQL
