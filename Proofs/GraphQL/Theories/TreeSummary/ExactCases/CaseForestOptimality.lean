import GraphQL.Theories.TreeSummary.ExactCasesOptimality
import Proofs.GraphQL.Theories.TreeSummary.ExactCases.Relation

/-! Optimality of the batched exact-case evaluator for supplied variables. -/

namespace GraphQL
namespace TreeSummary
namespace ExactCases

open GraphQL.ConditionTree
open GraphQL.Execution
open Optimality

universe u v

namespace CaseForestProof

-- A proof-local structural account of the batched evaluator. Public optimality uses
-- `CaseCursor.ContextOutcome`; this relation exists only to support induction over the
-- forest implementation before the concrete-environment lifting step.
mutual
  inductive ContextOutcome (semantics : OutcomeSemantics.{u}) (schema : Schema)
      : List BooleanLiteral -> CaseForest -> PossibleTypeRegion
        -> VariableValues -> VariableValues -> semantics.Summary -> Prop
    | booleanFrontier
      (inheritedBooleanCondition forest possibleTypes variableValues
        fixedVariableValues outcome)
      (hbranches : forest.hasUnresolvedBranches = true)
      (htypes : forest.typeBranchPossibleTypes.isEmpty = true)
      (houtcome
        : ContextOutcome semantics schema
            (CaseForest.extendBooleanCondition inheritedBooleanCondition
              forest.booleanVariables variableValues)
            (forest.resolveBranches possibleTypes variableValues) possibleTypes
            variableValues fixedVariableValues outcome)
      : ContextOutcome semantics schema inheritedBooleanCondition forest
          possibleTypes variableValues fixedVariableValues outcome
    | noRegion
      (inheritedBooleanCondition forest possibleTypes variableValues fixedVariableValues)
      (hbranches : forest.hasUnresolvedBranches = true)
      (htypes : forest.typeBranchPossibleTypes.isEmpty = false)
      (hregions : forest.typeRegions possibleTypes = [])
      : ContextOutcome semantics schema inheritedBooleanCondition forest
          possibleTypes variableValues fixedVariableValues semantics.empty
    | region
      (inheritedBooleanCondition forest possibleTypes variableValues
        fixedVariableValues selectedRegion outcome)
      (hbranches : forest.hasUnresolvedBranches = true)
      (htypes : forest.typeBranchPossibleTypes.isEmpty = false)
      (hregion : selectedRegion ∈ forest.typeRegions possibleTypes)
      (houtcome
        : ContextOutcome semantics schema
            (CaseForest.extendBooleanCondition inheritedBooleanCondition
              forest.booleanVariables variableValues)
            (forest.resolveBranches selectedRegion variableValues) selectedRegion
            variableValues fixedVariableValues outcome)
      : ContextOutcome semantics schema inheritedBooleanCondition forest
          possibleTypes variableValues fixedVariableValues outcome
    | fields
      (inheritedBooleanCondition forest possibleTypes variableValues
        fixedVariableValues outcome)
      (hbranches : forest.hasUnresolvedBranches = false)
      (houtcome
        : ContextFieldGroupsOutcome semantics schema
            (forest.fieldGroups inheritedBooleanCondition possibleTypes)
            variableValues fixedVariableValues outcome)
      : ContextOutcome semantics schema inheritedBooleanCondition forest
          possibleTypes variableValues fixedVariableValues outcome

  inductive ContextFieldGroupsOutcome (semantics : OutcomeSemantics.{u}) (schema : Schema)
      : List CollectedFieldGroup -> VariableValues -> VariableValues
        -> semantics.Summary -> Prop
    | nil (variableValues fixedVariableValues)
      : ContextFieldGroupsOutcome semantics schema [] variableValues
          fixedVariableValues semantics.empty
    | cons
      (group rest variableValues fixedVariableValues children fieldOutcome restOutcome)
      (hchildren
        : ContextChildTypesOutcome semantics schema group
            (childParentTypes schema group) variableValues fixedVariableValues children)
      (hfield : semantics.fieldOutcomes group children fieldOutcome)
      (hrest
        : ContextFieldGroupsOutcome semantics schema rest variableValues
            fixedVariableValues restOutcome)
      : ContextFieldGroupsOutcome semantics schema (group :: rest)
          variableValues fixedVariableValues
          (semantics.combine fieldOutcome restOutcome)

  inductive ContextChildTypesOutcome (semantics : OutcomeSemantics.{u}) (schema : Schema)
      : CollectedFieldGroup -> TypeNames -> VariableValues -> VariableValues
        -> semantics.Summary -> Prop
    | none (group variableValues fixedVariableValues)
      : ContextChildTypesOutcome semantics schema group [] variableValues
          fixedVariableValues semantics.empty
    | some
      (group parentTypes variableValues fixedVariableValues childParentType outcome)
      (hparentType : childParentType ∈ parentTypes)
      (houtcome
        : let childTree :=
            group.childTreeWithKnownFalsePruning schema childParentType
              fixedVariableValues
          ContextOutcome semantics schema
            group.childInheritedBooleanCondition (.ofConditionTree childTree)
            childTree.condition.possibleTypes variableValues fixedVariableValues outcome)
      : ContextChildTypesOutcome semantics schema group parentTypes
          variableValues fixedVariableValues outcome
end

def conditionTreeOutcomes (semantics : OutcomeSemantics.{u}) (schema : Schema)
    (inheritedBooleanCondition : List BooleanLiteral) (tree : Tree)
    (variableValues : VariableValues)
    (fixedVariableValues : VariableValues := variableValues)
    : OutcomeSet semantics.Summary :=
  ContextOutcome semantics schema inheritedBooleanCondition
    (.ofConditionTree tree) tree.condition.possibleTypes variableValues
    fixedVariableValues

def selectionSetOutcomes (semantics : OutcomeSemantics.{u}) (schema : Schema)
    (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
    (selectionSet : List Selection) (variableValues : VariableValues)
    : OutcomeSet semantics.Summary :=
  conditionTreeOutcomes semantics schema inheritedBooleanCondition
    (ConditionTree.ofSelectionSetInScopeWithKnownFalsePruning schema parentType
      inheritedBooleanCondition variableValues selectionSet)
    variableValues variableValues

@[reducible]
private def proofAlgebra (semantics : OutcomeSemantics.{u}) : Algebra.{u} :=
  {
    Summary := OutcomeSet semantics.Summary
    empty := OutcomeSet.singleton semantics.empty
    combine := OutcomeSet.combine semantics.combine
    field :=
      fun group children =>
        OutcomeSet.bind children (semantics.fieldOutcomes group)
    join := OutcomeSet.union
  }

private def relation {semantics : OutcomeSemantics.{u}} {abstract : Algebra.{v}}
    {le : abstract.Summary -> abstract.Summary -> Prop}
    (laws : BestTransferLaws semantics abstract le)
    : (proofAlgebra semantics).Relation abstract :=
  {
    related := BestBound le laws.approximates
    empty_related := laws.empty_best
    combine_related := fun _ _ _ _ => laws.combine_best _ _ _ _
    field_related := fun group _ _ => laws.field_best group _ _
    join_related := fun _ _ _ _ => laws.join_best _ _ _ _
  }

private theorem joinMap_iff
    (semantics : OutcomeSemantics.{u}) (items : List α)
    (summarize : ∀ item, item ∈ items -> OutcomeSet semantics.Summary)
    (outcome : semantics.Summary)
    : TreeSummary.joinMap (proofAlgebra semantics) items summarize outcome
      ↔ (items = [] ∧ outcome = semantics.empty)
        ∨ ∃ item hitem, summarize item hitem outcome := by
  induction items with
  | nil =>
      simp [TreeSummary.joinMap, proofAlgebra, OutcomeSet.singleton]
  | cons item rest ih =>
      cases rest with
      | nil =>
          simp [TreeSummary.joinMap]
      | cons next tail =>
          rw [TreeSummary.joinMap]
          change (summarize item _ outcome
                    ∨ TreeSummary.joinMap (proofAlgebra semantics) (next :: tail)
                        (fun candidate hcandidate =>
                          summarize candidate (by simp [hcandidate]))
                        outcome)
                  ↔ _
          rw [ih
            (fun candidate hcandidate => summarize candidate (by simp [hcandidate]))]
          simp only [List.cons_ne_nil, false_and, false_or]
          constructor
          · rintro (hitem | ⟨candidate, hcandidate, houtcome⟩)
            · exact ⟨item, by simp, hitem⟩
            · exact ⟨candidate, by simp [hcandidate], houtcome⟩
          · rintro ⟨candidate, hcandidate, houtcome⟩
            simp only [List.mem_cons] at hcandidate
            rcases hcandidate with rfl | hcandidate
            · exact Or.inl houtcome
            · have hmem : candidate ∈ next :: tail := by simp [hcandidate]
              exact Or.inr ⟨candidate, hmem, houtcome⟩

private theorem combineMap_iff
    (semantics : OutcomeSemantics.{u}) (items : List α)
    (summarize : ∀ item, item ∈ items -> OutcomeSet semantics.Summary)
    (outcome : semantics.Summary)
    : TreeSummary.combineMap (proofAlgebra semantics) items summarize outcome
      ↔ match items with
        | [] => outcome = semantics.empty
        | item :: rest =>
            ∃ itemOutcome restOutcome,
              summarize item (by simp) itemOutcome
              ∧ TreeSummary.combineMap (proofAlgebra semantics) rest
                  (fun candidate hcandidate =>
                    summarize candidate (by simp [hcandidate])) restOutcome
              ∧ outcome = semantics.combine itemOutcome restOutcome := by
  cases items with
  | nil => simp [TreeSummary.combineMap, proofAlgebra, OutcomeSet.singleton]
  | cons item rest =>
      rw [TreeSummary.combineMap]
      rfl

private theorem contextOutcome_iff_fold
    (semantics : OutcomeSemantics.{u}) (schema : Schema)
    (inheritedBooleanCondition : List BooleanLiteral)
    (forest : CaseForest) (possibleTypes : PossibleTypeRegion)
    (variableValues fixedVariableValues : VariableValues)
    (outcome : semantics.Summary)
    : ContextOutcome semantics schema inheritedBooleanCondition forest
        possibleTypes variableValues fixedVariableValues outcome
      ↔ CaseForest.summarize (proofAlgebra semantics) schema
          inheritedBooleanCondition forest possibleTypes variableValues
          fixedVariableValues outcome := by
  apply CaseForest.summarize.induct schema variableValues fixedVariableValues
    (motive1 := fun inherited forest possibleTypes =>
      ∀ outcome,
        ContextOutcome semantics schema inherited forest
            possibleTypes variableValues fixedVariableValues outcome
          ↔ CaseForest.summarize (proofAlgebra semantics) schema inherited
              forest possibleTypes variableValues fixedVariableValues outcome)
    (motive2 := fun groups =>
      ∀ outcome,
        ContextFieldGroupsOutcome semantics schema groups
            variableValues fixedVariableValues outcome
          ↔ CaseForest.summarizeFieldGroups (proofAlgebra semantics) schema
              groups variableValues fixedVariableValues outcome)
    (motive3 := fun group parentTypes =>
      ∀ outcome,
        ContextChildTypesOutcome semantics schema group parentTypes
            variableValues fixedVariableValues outcome
          ↔ CaseForest.summarizeChildTypes (proofAlgebra semantics) schema
              group parentTypes variableValues fixedVariableValues outcome)
    (motive4 := fun inherited forest regions hbranches =>
      ∀ outcome,
        ((regions = [] ∧ outcome = semantics.empty)
          ∨ ∃ region,
            region ∈ regions ∧
              ContextOutcome semantics schema
                (CaseForest.extendBooleanCondition inherited forest.booleanVariables
                  variableValues)
                (forest.resolveBranches region variableValues) region variableValues
                fixedVariableValues outcome)
          ↔ CaseForest.summarizeTypeRegions (proofAlgebra semantics) schema
              inherited forest regions variableValues hbranches fixedVariableValues
              outcome)
  case case1 =>
    intro inherited forest possibleTypes hbranches htypes ih outcome
    rw [CaseForest.summarize.eq_1]
    simp only [hbranches, dite_true, htypes, if_true]
    constructor
    · intro h
      cases h with
      | booleanFrontier _ _ _ _ _ _ _ _ houtcome => exact (ih outcome).mp houtcome
      | noRegion _ _ _ _ _ _ htypesFalse _ => simp [htypes] at htypesFalse
      | region _ _ _ _ _ _ _ _ htypesFalse _ _ => simp [htypes] at htypesFalse
      | fields _ _ _ _ _ _ hfalse => simp [hbranches] at hfalse
    · intro h
      exact .booleanFrontier inherited forest possibleTypes variableValues
        fixedVariableValues outcome hbranches htypes ((ih outcome).mpr h)
  case case2 =>
    intro inherited forest possibleTypes hbranches htypes ih outcome
    have htypesFalse : forest.typeBranchPossibleTypes.isEmpty = false := by
      cases hvalue : forest.typeBranchPossibleTypes.isEmpty with
      | false => rfl
      | true => exact (htypes hvalue).elim
    rw [CaseForest.summarize.eq_1]
    simp only [hbranches, dite_true, htypes, Bool.false_eq_true, if_false]
    constructor
    · intro h
      cases h with
      | booleanFrontier _ _ _ _ _ _ _ htypesTrue _ => simp [htypesFalse] at htypesTrue
      | noRegion _ _ _ _ _ _ _ hregions =>
          simpa only using (ih semantics.empty).mp (Or.inl ⟨hregions, rfl⟩)
      | region _ _ _ _ _ selectedRegion _ _ _ hregion houtcome =>
          exact (ih outcome).mp (Or.inr ⟨selectedRegion, hregion, houtcome⟩)
      | fields _ _ _ _ _ _ hfalse => simp [hbranches] at hfalse
    · intro h
      rcases (ih outcome).mpr h with ⟨hregions, rfl⟩ | ⟨region, hregion, houtcome⟩
      · exact .noRegion inherited forest possibleTypes variableValues
          fixedVariableValues hbranches htypesFalse hregions
      · exact .region inherited forest possibleTypes variableValues fixedVariableValues
          region outcome hbranches htypesFalse hregion houtcome
  case case3 =>
    intro inherited forest possibleTypes hbranches ih outcome
    rw [CaseForest.summarize.eq_1]
    simp only [hbranches]
    constructor
    · intro h
      cases h with
      | booleanFrontier _ _ _ _ _ _ htrue => exact (hbranches htrue).elim
      | noRegion _ _ _ _ _ htrue => exact (hbranches htrue).elim
      | region _ _ _ _ _ _ _ htrue => exact (hbranches htrue).elim
      | fields _ _ _ _ _ _ hfalse houtcome => exact (ih outcome).mp houtcome
    · intro h
      have hfalse : forest.hasUnresolvedBranches = false := by
        cases hvalue : forest.hasUnresolvedBranches
        · rfl
        · exact (hbranches hvalue).elim
      exact .fields inherited forest possibleTypes variableValues fixedVariableValues
        outcome hfalse ((ih outcome).mpr h)
  case case4 =>
    intro groups childIH outcome
    induction groups generalizing outcome with
    | nil =>
        simp only [CaseForest.summarizeFieldGroups.eq_1,
          TreeSummary.combineMap, proofAlgebra, OutcomeSet.singleton]
        constructor
        · intro h
          cases h
          rfl
        · intro h
          subst outcome
          exact .nil variableValues fixedVariableValues
    | cons group rest restIH =>
        rw [CaseForest.summarizeFieldGroups.eq_1]
        rw [TreeSummary.combineMap]
        simp only [proofAlgebra]
        change
          ContextFieldGroupsOutcome semantics schema
              (group :: rest) variableValues fixedVariableValues outcome
            ↔ OutcomeSet.combine semantics.combine
                (OutcomeSet.bind
                  (CaseForest.summarizeChildTypes (proofAlgebra semantics) schema
                    group (childParentTypes schema group) variableValues
                    fixedVariableValues)
                  (semantics.fieldOutcomes group))
                (TreeSummary.combineMap (proofAlgebra semantics) rest
                  (fun candidate hcandidate =>
                    OutcomeSet.bind
                      (CaseForest.summarizeChildTypes
                        (proofAlgebra semantics) schema candidate
                        (childParentTypes schema candidate) variableValues
                        fixedVariableValues)
                      (semantics.fieldOutcomes candidate))) outcome
        constructor
        · intro h
          cases h with
          | cons _ _ _ _ children fieldOutcome restOutcome hchildOutcome hfield hrest =>
              exact ⟨fieldOutcome, restOutcome,
                ⟨children, (childIH group (by simp) children).mp hchildOutcome, hfield⟩,
                (by
                  have hrestIH := restIH
                    (fun candidate hcandidate =>
                      childIH candidate (by simp [hcandidate])) restOutcome
                  rw [CaseForest.summarizeFieldGroups.eq_1] at hrestIH
                  exact hrestIH.mp hrest),
                rfl⟩
        · rintro ⟨fieldOutcome, restOutcome, ⟨children, hchildFold, hfield⟩,
              hrest, rfl⟩
          exact .cons group rest variableValues fixedVariableValues children fieldOutcome
            restOutcome ((childIH group (by simp) children).mpr hchildFold) hfield
            (by
              have hrestIH := restIH
                (fun candidate hcandidate =>
                  childIH candidate (by simp [hcandidate])) restOutcome
              rw [CaseForest.summarizeFieldGroups.eq_1] at hrestIH
              exact hrestIH.mpr hrest)
  case case5 =>
    intro group parentTypes ih outcome
    simp only [CaseForest.summarizeChildTypes.eq_1]
    rw [joinMap_iff semantics]
    constructor
    · intro h
      cases h with
      | none => exact Or.inl ⟨rfl, rfl⟩
      | some _ _ _ _ childParentType _ hparentType houtcome =>
          exact Or.inr ⟨childParentType, hparentType,
            (ih childParentType outcome).mp houtcome⟩
    · rintro (⟨rfl, rfl⟩ | ⟨childParentType, hparentType, houtcome⟩)
      · exact .none group variableValues fixedVariableValues
      · exact .some group parentTypes variableValues fixedVariableValues
          childParentType outcome hparentType
          ((ih childParentType outcome).mpr houtcome)
  case case6 =>
    intro inherited forest regions hbranches ih outcome
    simp only [CaseForest.summarizeTypeRegions.eq_1]
    rw [joinMap_iff semantics]
    apply or_congr Iff.rfl
    apply exists_congr
    intro region
    constructor
    · rintro ⟨hregion, houtcome⟩
      exact ⟨hregion, (ih region outcome).mp houtcome⟩
    · rintro ⟨hregion, houtcome⟩
      exact ⟨hregion, (ih region outcome).mpr houtcome⟩

private theorem conditionTreeOutcomes_iff_proofFold
    (semantics : OutcomeSemantics.{u}) (schema : Schema)
    (inheritedBooleanCondition : List BooleanLiteral) (tree : Tree)
    (variableValues fixedVariableValues : VariableValues)
    (outcome : semantics.Summary)
    : CaseForestProof.conditionTreeOutcomes semantics schema inheritedBooleanCondition
        tree variableValues fixedVariableValues outcome
      ↔ CaseForest.summarizeConditionTree (proofAlgebra semantics) schema
          inheritedBooleanCondition tree variableValues fixedVariableValues outcome := by
  exact contextOutcome_iff_fold semantics schema inheritedBooleanCondition
    (.ofConditionTree tree) tree.condition.possibleTypes variableValues
    fixedVariableValues outcome

private theorem bestBound_of_attainable_iff
    {ConcreteSummary : Type u} {AbstractSummary : Type v}
    {le : AbstractSummary -> AbstractSummary -> Prop}
    {related : ConcreteSummary -> AbstractSummary -> Prop}
    {left right : OutcomeSet ConcreteSummary} {estimate : AbstractSummary}
    (hiff : ∀ outcome, left outcome ↔ right outcome)
    (hbest : BestBound le related right estimate)
    : BestBound le related left estimate :=
  {
    feasible := by
      rcases hbest.feasible with ⟨outcome, houtcome⟩
      exact ⟨outcome, (hiff outcome).mpr houtcome⟩
    sound := fun outcome houtcome => hbest.sound outcome ((hiff outcome).mp houtcome)
    least :=
      fun candidate hcandidate =>
        hbest.least candidate
          fun outcome houtcome => hcandidate outcome ((hiff outcome).mpr houtcome)
  }

end CaseForestProof

theorem CaseForest.summarizeConditionTree_best
    {semantics : OutcomeSemantics.{u}} {abstract : Algebra.{v}}
    {le : abstract.Summary -> abstract.Summary -> Prop}
    (laws : BestTransferLaws semantics abstract le) (schema : Schema)
    (inheritedBooleanCondition : List BooleanLiteral) (tree : Tree)
    (variableValues fixedVariableValues : VariableValues)
    : BestBound le laws.approximates
        (CaseForestProof.conditionTreeOutcomes semantics schema inheritedBooleanCondition
          tree variableValues fixedVariableValues)
        (CaseForest.summarizeConditionTree abstract schema inheritedBooleanCondition tree
          variableValues fixedVariableValues) := by
  apply CaseForestProof.bestBound_of_attainable_iff
    (CaseForestProof.conditionTreeOutcomes_iff_proofFold semantics schema
      inheritedBooleanCondition tree variableValues fixedVariableValues)
  exact CaseForest.summarizeConditionTree_related
    (CaseForestProof.proofAlgebra semantics) abstract (CaseForestProof.relation laws) schema
    inheritedBooleanCondition tree variableValues fixedVariableValues

theorem CaseForest.summarizeSelectionSet_best
    {semantics : OutcomeSemantics.{u}} {abstract : Algebra.{v}}
    {le : abstract.Summary -> abstract.Summary -> Prop}
    (laws : BestTransferLaws semantics abstract le) (schema : Schema)
    (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
    (selectionSet : List Selection) (variableValues : VariableValues)
    : BestBound le laws.approximates
        (CaseForestProof.selectionSetOutcomes semantics schema parentType
          inheritedBooleanCondition selectionSet variableValues)
        (CaseForest.summarizeSelectionSet abstract schema parentType
          inheritedBooleanCondition selectionSet variableValues) := by
  unfold CaseForestProof.selectionSetOutcomes CaseForest.summarizeSelectionSet
  exact CaseForest.summarizeConditionTree_best laws schema inheritedBooleanCondition
    (ConditionTree.ofSelectionSetInScopeWithKnownFalsePruning schema parentType
      inheritedBooleanCondition variableValues selectionSet)
    variableValues variableValues

theorem summarizeOperationWithVariables_forest_best
    {semantics : OutcomeSemantics.{u}}
    (abstractFor : VariableValues -> Algebra.{v}) {schema : Schema}
    (variableValues : VariableValues) (operation : Operation)
    {le
      : (abstractFor (Execution.coerceVariableValues operation variableValues)).Summary
        -> (abstractFor (Execution.coerceVariableValues operation variableValues)).Summary
        -> Prop}
    (laws
      : BestTransferLaws semantics
          (abstractFor (Execution.coerceVariableValues operation variableValues)) le)
    : BestBound le laws.approximates
        (CaseForestProof.selectionSetOutcomes semantics schema
          (operation.rootType schema) [] operation.selectionSet
          (Execution.coerceVariableValues operation variableValues))
        (summarizeOperationWithVariables abstractFor schema variableValues
          operation) := by
  unfold summarizeOperationWithVariables
  exact CaseForest.summarizeSelectionSet_best laws schema (operation.rootType schema) []
    operation.selectionSet (Execution.coerceVariableValues operation variableValues)

end ExactCases
end TreeSummary
end GraphQL
