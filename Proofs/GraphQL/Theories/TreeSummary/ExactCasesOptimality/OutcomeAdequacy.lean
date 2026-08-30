import Proofs.GraphQL.Theories.TreeSummary.ExactCasesOptimality.BestBounds
import Proofs.GraphQL.Theories.TreeSummary.ExactCases.RuntimeCases

/-! Adequacy of the ExactCases relational outcome semantics. -/

namespace GraphQL
namespace TreeSummary
namespace ExactCases

open GraphQL.ConditionTree
open GraphQL.Execution
open GraphQL.Execution.FieldGroups
open Optimality
open Internal

universe u v w

-----------------------------------------------------------------------------------------
-- Relational outcome semantics: adequacy
-----------------------------------------------------------------------------------------

theorem selectionSetBooleanSplitExact
    (semantics : OutcomeSemantics.{u}) (schema : Schema) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (selectionSet : List Selection) (initial : BooleanEnvironment)
    (variableName : Name)
    : SelectionSetBooleanSplitExact semantics schema parentType
        inheritedBooleanCondition selectionSet initial variableName := by
  unfold SelectionSetBooleanSplitExact
  intro hstatus outcome
  simp only [selectionSetOutcomes, BooleanEnvironment.pruningValues_assign]
  unfold conditionTreeOutcomes
  constructor
  · rintro ⟨assignment, hmatches, houtcome⟩
    cases hvalue : assignment variableName with
    | false =>
        apply Or.inl
        have hassigned :=
          (BooleanEnvironment.matches_assign_iff initial assignment variableName false
            hstatus).mpr ⟨hmatches, hvalue⟩
        exact ⟨assignment, hassigned,
          houtcome.changeEnvironment hmatches
            (initial.assign variableName false) hassigned
            (BooleanEnvironment.pruningValues_assign initial variableName false)⟩
    | true =>
        apply Or.inr
        have hassigned :=
          (BooleanEnvironment.matches_assign_iff initial assignment variableName true
            hstatus).mpr ⟨hmatches, hvalue⟩
        exact ⟨assignment, hassigned,
          houtcome.changeEnvironment hmatches
            (initial.assign variableName true) hassigned
            (BooleanEnvironment.pruningValues_assign initial variableName true)⟩
  · rintro (⟨assignment, hmatches, houtcome⟩ | ⟨assignment, hmatches, houtcome⟩)
    · have hparts :=
        (BooleanEnvironment.matches_assign_iff initial assignment variableName false
          hstatus).mp hmatches
      exact ⟨assignment, hparts.1,
        houtcome.changeEnvironment hmatches initial hparts.1
          (BooleanEnvironment.pruningValues_assign initial variableName false).symm⟩
    · have hparts :=
        (BooleanEnvironment.matches_assign_iff initial assignment variableName true
          hstatus).mp hmatches
      exact ⟨assignment, hparts.1,
        houtcome.changeEnvironment hmatches initial hparts.1
          (BooleanEnvironment.pruningValues_assign initial variableName true).symm⟩

theorem selectionSetResolvedAssignmentsExact
    (semantics : OutcomeSemantics.{u}) (schema : Schema) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (selectionSet : List Selection) (initial : BooleanEnvironment)
    : SelectionSetResolvedAssignmentsExact semantics schema parentType
        inheritedBooleanCondition selectionSet initial := by
  unfold SelectionSetResolvedAssignmentsExact
  dsimp only
  intro outcome
  simp only [selectionSetOutcomes, BooleanEnvironment.pruningValues_assignVariables]
  unfold conditionTreeOutcomes
  constructor
  · rintro ⟨assignment, hmatches, houtcome⟩
    let variables :=
      (conditionTreeBooleanVariables
        (ConditionTree.ofSelectionSetInScopeWithKnownFalsePruning schema parentType
          inheritedBooleanCondition initial.pruningValues selectionSet)).eraseDups
    let resolved := initial.assignVariables variables assignment
    have hresolved : assignment.Extends resolved :=
      BooleanEnvironment.extends_assignVariables_self assignment variables initial hmatches
    refine ⟨assignment, hmatches, assignment, hresolved, ?_⟩
    exact houtcome.changeEnvironment hmatches resolved hresolved
      (BooleanEnvironment.pruningValues_assignVariables initial assignment variables)
  · rintro ⟨selectedAssignment, hselected, assignment, hmatches, houtcome⟩
    let variables :=
      (conditionTreeBooleanVariables
        (ConditionTree.ofSelectionSetInScopeWithKnownFalsePruning schema parentType
          inheritedBooleanCondition initial.pruningValues selectionSet)).eraseDups
    let resolved := initial.assignVariables variables selectedAssignment
    have hrefines : BooleanEnvironment.Refines resolved initial :=
      BooleanEnvironment.assignVariables_self_refines selectedAssignment variables initial
        hselected
    have hinitial : assignment.Extends initial :=
      BooleanEnvironment.extends_of_refines hmatches hrefines
    refine ⟨assignment, hinitial, ?_⟩
    exact houtcome.changeEnvironment hmatches initial hinitial
      (BooleanEnvironment.pruningValues_assignVariables initial selectedAssignment
        variables).symm

-- The unit algebra turns the generic best-bound theorem into a pure inhabitance
-- argument. Keeping this witness separate makes the public inhabitance theorem state
-- only its genuine local premise.
private def inhabitanceAlgebra : Algebra :=
  {
    Summary := Unit
    empty := ()
    combine := fun _left _right => ()
    field := fun _group _children => ()
    join := fun _left _right => ()
  }

private def inhabitanceTransferLaws
    (semantics : OutcomeSemantics.{u})
    (hfieldOutcomes : semantics.FieldOutcomesInhabited)
    : BestTransferLaws semantics inhabitanceAlgebra (fun _left _right => True) := by
  refine {
    approximates := fun _concrete _abstract => True
    empty_best := ?_
    combine_best := ?_
    field_best := ?_
    join_best := ?_
  }
  · exact {
      feasible := ⟨semantics.empty, rfl⟩
      sound := fun _outcome _houtcome => trivial
      least := fun _candidate _hbound => trivial
    }
  · intro left right _abstractLeft _abstractRight hleft hright
    refine {
      feasible := ?_
      sound := fun _outcome _houtcome => trivial
      least := fun _candidate _hbound => trivial
    }
    rcases hleft.feasible with ⟨leftOutcome, hleftOutcome⟩
    rcases hright.feasible with ⟨rightOutcome, hrightOutcome⟩
    exact ⟨semantics.combine leftOutcome rightOutcome,
      ⟨leftOutcome, rightOutcome, hleftOutcome, hrightOutcome, rfl⟩⟩
  · intro group children _abstractChildren hchildren
    refine {
      feasible := ?_
      sound := fun _outcome _houtcome => trivial
      least := fun _candidate _hbound => trivial
    }
    rcases hchildren.feasible with ⟨childrenOutcome, hchildrenOutcome⟩
    rcases hfieldOutcomes group childrenOutcome with ⟨fieldOutcome, hfieldOutcome⟩
    exact ⟨fieldOutcome, ⟨childrenOutcome, hchildrenOutcome, hfieldOutcome⟩⟩
  · intro left _right _abstractLeft _abstractRight hleft _hright
    refine {
      feasible := ?_
      sound := fun _outcome _houtcome => trivial
      least := fun _candidate _hbound => trivial
    }
    rcases hleft.feasible with ⟨outcome, houtcome⟩
    exact ⟨outcome, Or.inl houtcome⟩

theorem selectionSetOutcomesInhabited
    (semantics : OutcomeSemantics.{u}) (schema : Schema) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (selectionSet : List Selection) (initial : BooleanEnvironment)
    : SelectionSetOutcomesInhabited semantics schema parentType
        inheritedBooleanCondition selectionSet initial := by
  unfold SelectionSetOutcomesInhabited OutcomeSemantics.FieldOutcomesInhabited
  intro hfieldOutcomes
  exact (summarizeSelectionSet_best
    (inhabitanceTransferLaws semantics hfieldOutcomes) schema parentType
    inheritedBooleanCondition selectionSet initial).feasible

@[reducible]
private def runtimeGroupSemantics : OutcomeSemantics :=
  OutcomeSemantics.boundaryFieldGroups

private def runtimeFieldGroupsFrom
    (inheritedBooleanCondition caseCondition : List BooleanLiteral)
    (cursor : CaseCursor) (possibleTypes : PossibleTypeRegion)
    (runtimeType : Name) (variableValues : VariableValues)
    : List CollectedFieldGroup :=
  let resolved :=
    RuntimeCase.resolve inheritedBooleanCondition caseCondition cursor possibleTypes
      runtimeType variableValues
  resolved.cursor.fieldGroups resolved.inheritedBooleanCondition resolved.possibleTypes

private theorem RuntimeCase.resolve_eq_typeBranch
    (inheritedBooleanCondition caseCondition : List BooleanLiteral)
    (cursor : CaseCursor) (possibleTypes : PossibleTypeRegion)
    (runtimeType : Name) (variableValues : VariableValues)
    (branch : Branch Tree) (rest : List (Branch Tree)) (typeName : Name)
    (hbranches : cursor.pendingBranches = branch :: rest)
    (hcondition : branch.condition = .typeCondition typeName)
    : resolve inheritedBooleanCondition caseCondition cursor possibleTypes runtimeType
        variableValues
      = let region :=
          chooseTypeRegion runtimeType possibleTypes
            (possibleTypeRegions possibleTypes [branch.body.condition.possibleTypes])
        resolve inheritedBooleanCondition caseCondition
          (if possibleTypesSubset region branch.body.condition.possibleTypes then
              cursor.selectBranch branch.body rest
            else
              cursor.skipBranch rest)
          region runtimeType variableValues := by
  rw [resolve.eq_1]
  split <;> rename_i hactual
  · simp_all
  · obtain ⟨rfl, rfl⟩ := List.cons.inj (hbranches.symm.trans hactual)
    simp only [hcondition]

private theorem RuntimeCase.resolve_eq_booleanBranch
    (inheritedBooleanCondition caseCondition : List BooleanLiteral)
    (cursor : CaseCursor) (possibleTypes : PossibleTypeRegion)
    (runtimeType : Name) (variableValues : VariableValues)
    (branch : Branch Tree) (rest : List (Branch Tree)) (literal : BooleanLiteral)
    (hbranches : cursor.pendingBranches = branch :: rest)
    (hcondition : branch.condition = .booleanLiteral literal)
    : resolve inheritedBooleanCondition caseCondition cursor possibleTypes runtimeType
        variableValues
      = let value :=
          (inputValueBoolean? variableValues (.variable literal.variableName)).getD false
        let selectedLiteral :=
          if value then
            BooleanLiteral.positive literal.variableName
          else
            BooleanLiteral.negative literal.variableName
        resolve inheritedBooleanCondition (selectedLiteral :: caseCondition)
          (cursor.resolveBooleanBranch branch.body rest literal value)
          possibleTypes runtimeType variableValues := by
  rw [resolve.eq_1]
  split <;> rename_i hactual
  · simp_all
  · obtain ⟨rfl, rfl⟩ := List.cons.inj (hbranches.symm.trans hactual)
    simp only [hcondition]

private theorem RuntimeCase.resolve_eq_fields
    (inheritedBooleanCondition caseCondition : List BooleanLiteral)
    (cursor : CaseCursor) (possibleTypes : PossibleTypeRegion)
    (runtimeType : Name) (variableValues : VariableValues)
    (hbranches : cursor.pendingBranches = [])
    : resolve inheritedBooleanCondition caseCondition cursor possibleTypes runtimeType
        variableValues
      = {
        cursor
        possibleTypes
        inheritedBooleanCondition :=
          extendBooleanCondition inheritedBooleanCondition caseCondition
      } := by
  rw [resolve.eq_1]
  split <;> rename_i hactual
  · rfl
  · simp_all

private theorem BooleanEnvironment.concrete_statusForVariable_some
    (variableValues : VariableValues) (variableName : Name)
    : (BooleanEnvironment.concrete variableValues).statusForVariable variableName
      = some
          ((inputValueBoolean? variableValues (.variable variableName)).getD false) := by
  rw [BooleanEnvironment.concrete_statusForVariable]
  cases hvalue : inputValueBoolean? variableValues (.variable variableName)
    <;> simp

private theorem BooleanAssignment.eq_of_extends_complete
    (left right : BooleanAssignment) (variableValues : VariableValues)
    (hleft : left.Extends (BooleanEnvironment.concrete variableValues))
    (hright : right.Extends (BooleanEnvironment.concrete variableValues))
    : left = right := by
  funext variableName
  let value :=
    (inputValueBoolean? variableValues (.variable variableName)).getD false
  have hstatus :
      (BooleanEnvironment.concrete variableValues).statusForVariable variableName
        = some value := by
    exact BooleanEnvironment.concrete_statusForVariable_some variableValues variableName
  exact (hleft variableName value hstatus).trans
    (hright variableName value hstatus).symm

private theorem contextFieldGroupsOutcome_runtimeGroupSemantics_exists
    (schema : Schema) (assignment : BooleanAssignment)
    (variableValues : VariableValues)
    (hassignment : assignment.Extends (BooleanEnvironment.concrete variableValues))
    (groups : List CollectedFieldGroup)
    : CaseCursor.ContextFieldGroupsOutcome runtimeGroupSemantics schema assignment
        (BooleanEnvironment.concrete variableValues) groups groups := by
  induction groups with
  | nil =>
      exact .nil assignment (BooleanEnvironment.concrete variableValues)
  | cons group rest ih =>
      have hchildren :
          ∃ children,
            CaseCursor.ContextChildTypesOutcome runtimeGroupSemantics schema assignment
              (BooleanEnvironment.concrete variableValues) group
              (childParentTypes schema group) children := by
        cases hparentTypes : childParentTypes schema group with
        | nil =>
            exact ⟨[], .none assignment
              (BooleanEnvironment.concrete variableValues) group⟩
        | cons childParentType remainingParentTypes =>
            have hinhabited := selectionSetOutcomesInhabited runtimeGroupSemantics schema
              childParentType group.childInheritedBooleanCondition
              group.mergedSelectionSet (BooleanEnvironment.concrete variableValues)
              (by
                intro candidateGroup children
                unfold runtimeGroupSemantics OutcomeSemantics.boundaryFieldGroups
                exact ⟨[candidateGroup], by
                  simp [OutcomeSet.singleton]⟩)
            rcases hinhabited with
              ⟨children, childAssignment, hchildAssignment, hchildOutcome⟩
            have hequal := BooleanAssignment.eq_of_extends_complete childAssignment
              assignment variableValues hchildAssignment hassignment
            subst childAssignment
            refine ⟨children, .some assignment
              (BooleanEnvironment.concrete variableValues) group
              (childParentType :: remainingParentTypes) childParentType children
              (by simp) ?_⟩
            unfold CollectedFieldGroup.childTreeWithKnownFalsePruning
            simpa [selectionSetOutcomes, conditionTreeOutcomes] using hchildOutcome
      rcases hchildren with ⟨children, hchildren⟩
      have hfield : runtimeGroupSemantics.fieldOutcomes group children [group] := by
        unfold runtimeGroupSemantics OutcomeSemantics.boundaryFieldGroups
        simp [OutcomeSet.singleton]
      exact .cons assignment (BooleanEnvironment.concrete variableValues) group rest
        children [group] rest hchildren hfield ih

private theorem contextOutcome_runtimeGroupSemantics_forRuntimeType
    (schema : Schema) (assignment : BooleanAssignment)
    (variableValues : VariableValues)
    (hassignment : assignment.Extends (BooleanEnvironment.concrete variableValues))
    (inheritedBooleanCondition caseCondition : List BooleanLiteral)
    (cursor : CaseCursor) (possibleTypes : PossibleTypeRegion)
    (runtimeType : Name) (hruntime : runtimeType ∈ possibleTypes)
    : ∃ groups,
        CaseCursor.ContextOutcome runtimeGroupSemantics schema assignment
          (BooleanEnvironment.concrete variableValues) inheritedBooleanCondition
          caseCondition cursor possibleTypes groups
        ∧ runtimeFieldGroupsFrom inheritedBooleanCondition caseCondition
            cursor possibleTypes runtimeType variableValues
          = groups := by
  apply RuntimeCase.resolve.induct runtimeType variableValues
    (motive := fun caseCondition cursor possibleTypes =>
      runtimeType ∈ possibleTypes ->
      ∃ groups,
        CaseCursor.ContextOutcome runtimeGroupSemantics schema assignment
          (BooleanEnvironment.concrete variableValues) inheritedBooleanCondition
          caseCondition cursor possibleTypes groups
        ∧ runtimeFieldGroupsFrom inheritedBooleanCondition caseCondition
            cursor possibleTypes runtimeType variableValues = groups)
  case case1 =>
    intro caseCondition cursor possibleTypes hbranches _hruntime
    let groups := cursor.fieldGroups
      (extendBooleanCondition inheritedBooleanCondition caseCondition) possibleTypes
    refine ⟨groups, ?_, ?_⟩
    · apply CaseCursor.ContextOutcome.fields
        (semantics := runtimeGroupSemantics) (schema := schema)
        assignment (BooleanEnvironment.concrete variableValues)
        inheritedBooleanCondition caseCondition cursor possibleTypes groups hbranches
      exact contextFieldGroupsOutcome_runtimeGroupSemantics_exists schema assignment
        variableValues hassignment groups
    · rw [runtimeFieldGroupsFrom,
        RuntimeCase.resolve_eq_fields _ _ _ _ _ _ hbranches]
  case case2 =>
    intro caseCondition cursor possibleTypes branch rest hbranches typeName hcondition
    dsimp only
    intro ih hruntime
    have hregion := RuntimeCase.chooseTypeRegion_mem possibleTypes
      [branch.body.condition.possibleTypes] runtimeType hruntime
    cases hselected : possibleTypesSubset
        (RuntimeCase.chooseTypeRegion runtimeType possibleTypes
          (possibleTypeRegions possibleTypes [branch.body.condition.possibleTypes]))
        branch.body.condition.possibleTypes with
    | false =>
        simp only [hselected] at ih
        rcases ih hregion.2 with ⟨groups, houtcome, hequal⟩
        refine ⟨groups, ?_, ?_⟩
        · exact CaseCursor.ContextOutcome.skipTypeRegion
            (semantics := runtimeGroupSemantics) (schema := schema) assignment
            (BooleanEnvironment.concrete variableValues) inheritedBooleanCondition
            caseCondition cursor possibleTypes branch rest typeName _ groups hbranches
            hcondition hregion.1 hselected houtcome
        rw [runtimeFieldGroupsFrom,
          RuntimeCase.resolve_eq_typeBranch _ _ _ _ _ _ _ _ _ hbranches hcondition]
        dsimp only
        simp only [hselected, Bool.false_eq_true, ↓reduceIte]
        simp only [Bool.false_eq_true, ↓reduceDIte] at hequal
        simpa only [runtimeFieldGroupsFrom] using hequal
    | true =>
        simp only [hselected, ↓reduceDIte] at ih
        rcases ih hregion.2 with ⟨groups, houtcome, hequal⟩
        refine ⟨groups, ?_, ?_⟩
        · exact CaseCursor.ContextOutcome.selectTypeRegion
            (semantics := runtimeGroupSemantics) (schema := schema) assignment
            (BooleanEnvironment.concrete variableValues) inheritedBooleanCondition
            caseCondition cursor possibleTypes branch rest typeName _ groups hbranches
            hcondition hregion.1 hselected houtcome
        rw [runtimeFieldGroupsFrom,
          RuntimeCase.resolve_eq_typeBranch _ _ _ _ _ _ _ _ _ hbranches hcondition]
        dsimp only
        simp only [hselected, ↓reduceIte]
        simpa only [runtimeFieldGroupsFrom] using hequal
  case case3 =>
    intro caseCondition cursor possibleTypes branch rest hbranches literal hcondition
    dsimp only
    intro ih hruntime
    let value :=
      (inputValueBoolean? variableValues (.variable literal.variableName)).getD false
    rcases ih hruntime with ⟨groups, houtcome, hequal⟩
    have hstatus :
        (BooleanEnvironment.concrete variableValues).statusForVariable
            literal.variableName
          = some value := by
      exact BooleanEnvironment.concrete_statusForVariable_some variableValues
        literal.variableName
    refine ⟨groups, ?_, ?_⟩
    · apply CaseCursor.ContextOutcome.knownBoolean
        (semantics := runtimeGroupSemantics) (schema := schema) assignment
        (BooleanEnvironment.concrete variableValues) inheritedBooleanCondition
        caseCondition cursor possibleTypes branch rest literal value groups hbranches
        hcondition hstatus
      simpa [value] using houtcome
    · rw [runtimeFieldGroupsFrom,
        RuntimeCase.resolve_eq_booleanBranch _ _ _ _ _ _ _ _ _ hbranches hcondition]
      dsimp only
      by_cases hvalue : value = true
      · simp only [value] at hvalue
        simp only [hvalue, ↓reduceDIte] at hequal
        simp only [hvalue, ↓reduceIte]
        simpa only [runtimeFieldGroupsFrom] using hequal
      · have hvalueFalse : value = false := by
          cases hactual : value
          · rfl
          · exact False.elim (hvalue hactual)
        simp only [value] at hvalueFalse
        simp only [hvalueFalse, Bool.false_eq_true, ↓reduceDIte] at hequal
        simp only [hvalueFalse, Bool.false_eq_true, ↓reduceIte]
        simpa only [runtimeFieldGroupsFrom] using hequal
  exact hruntime

private theorem runtimeCaseFieldGroups_representRuntimeGroups
    (schema : Schema) (variableValues : VariableValues) (parentType runtimeType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (selectionSet : List Selection)
    (hinherited : booleanConditionAllows variableValues inheritedBooleanCondition = true)
    (hincludes : schema.typeIncludesObject parentType runtimeType)
    : let tree :=
        ConditionTree.ofSelectionSetInScopeWithKnownFalsePruning schema parentType
          inheritedBooleanCondition variableValues selectionSet
      let groups :=
        RuntimeCase.fieldGroups parentType inheritedBooleanCondition
          (.ofConditionTree tree) tree.condition.possibleTypes runtimeType variableValues
      let runtimeGroups :=
        collectFields schema variableValues runtimeType
          (.object runtimeType () : ResolverValue Unit) selectionSet
      CollectedGroupsMatchRuntimeGroups runtimeType groups runtimeGroups := by
  let tree :=
    ConditionTree.ofSelectionSetInScopeWithKnownFalsePruning schema parentType
      inheritedBooleanCondition variableValues selectionSet
  let groups :=
    RuntimeCase.fieldGroups parentType inheritedBooleanCondition
      (.ofConditionTree tree) tree.condition.possibleTypes runtimeType variableValues
  let runtimeGroups :=
    collectFields schema variableValues runtimeType
      (.object runtimeType () : ResolverValue Unit) selectionSet
  have hmatch : ConditionTree.BooleanValuesMatchForPruning variableValues variableValues := by
    intro variableName value hvalue
    simp [hvalue]
  have hequivalent :=
    runtimeCaseGroupsWithVariables_permutationEquivalent_of_perm schema parentType
      runtimeType runtimeType inheritedBooleanCondition (List.Perm.refl selectionSet)
      variableValues variableValues hmatch () hinherited
      (List.contains_iff_mem.mpr hincludes)
  change RuntimeGroupsPermutationEquivalent
    (groups.map (RuntimeCase.collectedFieldGroupToExecutableGroup runtimeType))
    runtimeGroups at hequivalent
  exact {
    keysPerm := by
      rw [← RuntimeCase.collectedFieldGroupToExecutableGroup_keys]
      exact hequivalent.keysPerm
    fieldsPerm := by
      unfold RuntimeCase.collectedFieldGroupToExecutableGroup at hequivalent
      exact hequivalent.fieldsPerm
  }

private theorem contextFieldGroupsOutcome_runtimeGroupSemantics_eq
    {schema : Schema} {assignment : BooleanAssignment}
    {environment : BooleanEnvironment} {groups : List CollectedFieldGroup}
    {outcome : runtimeGroupSemantics.Summary}
    (houtcome
      : CaseCursor.ContextFieldGroupsOutcome runtimeGroupSemantics schema assignment
          environment groups outcome)
    : outcome = groups := by
  apply @CaseCursor.ContextFieldGroupsOutcome.rec runtimeGroupSemantics schema assignment
    (motive_1 := fun _environment _inherited _caseCondition _cursor _possibleTypes
      _outcome _h => True)
    (motive_2 := fun _environment groups outcome _h => outcome = groups)
    (motive_3 := fun _environment _group _parentTypes _outcome _h => True)
  case nil =>
    intro environment
    rfl
  case cons =>
    intro environment group rest children fieldOutcome restOutcome _hchildren hfield
      _hrest _ihChildren ihRest
    unfold runtimeGroupSemantics OutcomeSemantics.boundaryFieldGroups at fieldOutcome
    have hfieldOutcome : fieldOutcome = [group] := by
      unfold runtimeGroupSemantics OutcomeSemantics.boundaryFieldGroups at hfield
      simpa [OutcomeSet.singleton] using hfield
    subst fieldOutcome
    rw [ihRest]
    rfl
  all_goals try { intros <;> trivial }

private theorem contextOutcome_runtimeGroupSemantics_hasRuntimeType
    {schema : Schema} (variableValues : VariableValues)
    {assignment : BooleanAssignment}
    {inheritedBooleanCondition caseCondition : List BooleanLiteral}
    {cursor : CaseCursor} {possibleTypes : PossibleTypeRegion}
    {groups : runtimeGroupSemantics.Summary}
    (houtcome
      : CaseCursor.ContextOutcome runtimeGroupSemantics schema assignment
          (BooleanEnvironment.concrete variableValues) inheritedBooleanCondition
          caseCondition cursor possibleTypes groups)
    (hpossibleTypes : possibleTypes ≠ [])
    : ∃ runtimeType,
        runtimeType ∈ possibleTypes
        ∧ runtimeFieldGroupsFrom inheritedBooleanCondition caseCondition
            cursor possibleTypes runtimeType variableValues
          = groups := by
  apply @CaseCursor.ContextOutcome.rec runtimeGroupSemantics schema assignment
    (motive_1 := fun environment inherited _caseCondition cursor possibleTypes groups _h =>
      environment = BooleanEnvironment.concrete variableValues
      -> possibleTypes ≠ []
      -> ∃ runtimeType,
          runtimeType ∈ possibleTypes
          ∧ runtimeFieldGroupsFrom inherited _caseCondition cursor
              possibleTypes runtimeType variableValues = groups)
    (motive_2 := fun _environment groups outcome _h => outcome = groups)
    (motive_3 := fun _environment _group _parentTypes _outcome _h => True)
  case noTypeRegion =>
    intro environment inherited caseCondition cursor possibleTypes branch rest typeName
      hbranches hcondition hregions _henvironment hnonempty
    rcases possibleTypes with _ | ⟨runtimeType, restTypes⟩
    · exact False.elim (hnonempty rfl)
    · have hcovered :=
        (possibleTypeRegions_exact (runtimeType :: restTypes)
          [branch.body.condition.possibleTypes]).2.1 runtimeType (by simp)
      rw [hregions] at hcovered
      simp at hcovered
  case selectTypeRegion =>
    intro environment inherited caseCondition cursor possibleTypes branch rest typeName
      region outcome hbranches hcondition hregion hselected _houtcome ih henvironment
      _hnonempty
    have hexact :=
      possibleTypeRegions_exact possibleTypes [branch.body.condition.possibleTypes]
    rcases ih henvironment (hexact.1 region hregion).1 with
      ⟨runtimeType, hruntimeRegion, hequal⟩
    have hruntimePossible : runtimeType ∈ possibleTypes :=
      (hexact.1 region hregion).2 runtimeType hruntimeRegion
    have hregionEq :
        RuntimeCase.chooseTypeRegion runtimeType possibleTypes
            (possibleTypeRegions possibleTypes [branch.body.condition.possibleTypes])
          = region :=
      RuntimeCase.chooseTypeRegion_eq_of_mem possibleTypes
        [branch.body.condition.possibleTypes] runtimeType region hruntimePossible
        hregion hruntimeRegion
    refine ⟨runtimeType, hruntimePossible, ?_⟩
    change List CollectedFieldGroup at outcome
    rw [runtimeFieldGroupsFrom,
      RuntimeCase.resolve_eq_typeBranch _ _ _ _ _ _ _ _ _ hbranches hcondition]
    dsimp only
    rw [hregionEq, hselected]
    simp only [↓reduceIte]
    simpa only [runtimeFieldGroupsFrom] using hequal
  case skipTypeRegion =>
    intro environment inherited caseCondition cursor possibleTypes branch rest typeName
      region outcome hbranches hcondition hregion hskipped _houtcome ih henvironment
      _hnonempty
    have hexact :=
      possibleTypeRegions_exact possibleTypes [branch.body.condition.possibleTypes]
    rcases ih henvironment (hexact.1 region hregion).1 with
      ⟨runtimeType, hruntimeRegion, hequal⟩
    have hruntimePossible : runtimeType ∈ possibleTypes :=
      (hexact.1 region hregion).2 runtimeType hruntimeRegion
    have hregionEq :
        RuntimeCase.chooseTypeRegion runtimeType possibleTypes
            (possibleTypeRegions possibleTypes [branch.body.condition.possibleTypes])
          = region :=
      RuntimeCase.chooseTypeRegion_eq_of_mem possibleTypes
        [branch.body.condition.possibleTypes] runtimeType region hruntimePossible
        hregion hruntimeRegion
    refine ⟨runtimeType, hruntimePossible, ?_⟩
    change List CollectedFieldGroup at outcome
    rw [runtimeFieldGroupsFrom,
      RuntimeCase.resolve_eq_typeBranch _ _ _ _ _ _ _ _ _ hbranches hcondition]
    dsimp only
    rw [hregionEq, hskipped]
    simp only [Bool.false_eq_true, ↓reduceIte]
    simpa only [runtimeFieldGroupsFrom] using hequal
  case knownBoolean =>
    intro environment inherited caseCondition cursor possibleTypes branch rest literal
      value outcome hbranches hcondition hstatus _houtcome ih henvironment hnonempty
    subst environment
    rcases ih rfl hnonempty with ⟨runtimeType, hruntime, hequal⟩
    have hvalue :
        (inputValueBoolean? variableValues (.variable literal.variableName)).getD false
          = value := by
      rw [BooleanEnvironment.concrete_statusForVariable] at hstatus
      cases hlookup : inputValueBoolean? variableValues (.variable literal.variableName)
        <;> simp_all
    refine ⟨runtimeType, hruntime, ?_⟩
    change List CollectedFieldGroup at outcome
    rw [runtimeFieldGroupsFrom,
      RuntimeCase.resolve_eq_booleanBranch _ _ _ _ _ _ _ _ _ hbranches hcondition]
    dsimp only
    simp only [hvalue]
    simpa only [runtimeFieldGroupsFrom] using hequal
  case splitBoolean =>
    intro environment inherited caseCondition cursor possibleTypes branch rest literal
      outcome hbranches hcondition hstatus _houtcome ih henvironment _hnonempty
    subst environment
    rw [BooleanEnvironment.concrete_statusForVariable] at hstatus
    split at hstatus <;> contradiction
  case fields =>
    intro environment inherited caseCondition cursor possibleTypes outcome hbranches
      _hgroups hgroupsEq henvironment hnonempty
    subst environment
    rcases possibleTypes with _ | ⟨runtimeType, restTypes⟩
    · exact False.elim (hnonempty rfl)
    · refine ⟨runtimeType, by simp, ?_⟩
      subst outcome
      rw [runtimeFieldGroupsFrom,
        RuntimeCase.resolve_eq_fields _ _ _ _ _ _ hbranches]
  case nil =>
    intro environment
    rfl
  case cons =>
    intro environment group rest children fieldOutcome restOutcome _hchildren hfield
      _hrest _ihChildren ihRest
    unfold runtimeGroupSemantics OutcomeSemantics.boundaryFieldGroups at fieldOutcome
    have hfieldOutcome : fieldOutcome = [group] := by
      unfold runtimeGroupSemantics OutcomeSemantics.boundaryFieldGroups at hfield
      simpa [OutcomeSet.singleton] using hfield
    subst fieldOutcome
    rw [ihRest]
    rfl
  all_goals try { intros <;> trivial }
  all_goals first | exact houtcome | exact rfl | exact hpossibleTypes

-- At a concrete request context, the relational cursor semantics is exactly the
-- deterministic runtime path for one type in the current region. The two directional
-- induction lemmas above are implementation details of this characterization.
private theorem contextOutcome_runtimeGroupSemantics_iff_runtimeType
    {schema : Schema} (assignment : BooleanAssignment)
    (variableValues : VariableValues)
    (hassignment : assignment.Extends (BooleanEnvironment.concrete variableValues))
    (inheritedBooleanCondition caseCondition : List BooleanLiteral)
    (cursor : CaseCursor) (possibleTypes : PossibleTypeRegion)
    (groups : List CollectedFieldGroup) (hpossibleTypes : possibleTypes ≠ [])
    : CaseCursor.ContextOutcome runtimeGroupSemantics schema assignment
        (BooleanEnvironment.concrete variableValues) inheritedBooleanCondition
        caseCondition cursor possibleTypes groups
      ↔ ∃ runtimeType,
          runtimeType ∈ possibleTypes
          ∧ runtimeFieldGroupsFrom inheritedBooleanCondition caseCondition
              cursor possibleTypes runtimeType variableValues
            = groups := by
  constructor
  · intro houtcome
    exact contextOutcome_runtimeGroupSemantics_hasRuntimeType variableValues houtcome
      hpossibleTypes
  · rintro ⟨runtimeType, hruntimeType, hequal⟩
    rcases contextOutcome_runtimeGroupSemantics_forRuntimeType schema assignment
        variableValues hassignment inheritedBooleanCondition caseCondition cursor
        possibleTypes runtimeType hruntimeType with
      ⟨runtimeGroups, houtcome, hruntimeGroups⟩
    have : runtimeGroups = groups := hruntimeGroups.symm.trans hequal
    simpa only [this] using houtcome

theorem selectionSetRuntimeGroupsExact
    (schema : Schema) (variableValues : VariableValues) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (selectionSet : List Selection)
    : SelectionSetRuntimeGroupsExact schema variableValues parentType
        inheritedBooleanCondition selectionSet := by
  unfold SelectionSetRuntimeGroupsExact
  dsimp only
  intro hscope hinherited
  let tree :=
    ConditionTree.ofSelectionSetInScopeWithKnownFalsePruning schema parentType
      inheritedBooleanCondition variableValues selectionSet
  have htreePossibleTypes :
      tree.condition.possibleTypes = schema.getPossibleTypes parentType := by
    unfold tree ConditionTree.ofSelectionSetInScopeWithKnownFalsePruning
      ConditionTree.ofSelectionSetInScope
    rw [ConditionTree.Tree.insertSelections_condition]
    rfl
  have htreeNonempty : tree.condition.possibleTypes ≠ [] := by
    rcases hscope with ⟨runtimeType, hruntimeType⟩
    rw [htreePossibleTypes]
    exact List.ne_nil_of_mem hruntimeType
  constructor
  · intro runtimeType hincludes
    rcases BooleanEnvironment.exists_matches
        (BooleanEnvironment.concrete variableValues) with
      ⟨assignment, hassignment⟩
    have hruntimeTree : runtimeType ∈ tree.condition.possibleTypes := by
      rw [htreePossibleTypes]
      exact hincludes
    let groups :=
      runtimeFieldGroupsFrom inheritedBooleanCondition [] (.ofConditionTree tree)
        tree.condition.possibleTypes runtimeType variableValues
    have houtcome :
        CaseCursor.ContextOutcome runtimeGroupSemantics schema assignment
          (BooleanEnvironment.concrete variableValues) inheritedBooleanCondition []
          (.ofConditionTree tree) tree.condition.possibleTypes groups :=
      (contextOutcome_runtimeGroupSemantics_iff_runtimeType assignment variableValues
        hassignment inheritedBooleanCondition [] (.ofConditionTree tree)
        tree.condition.possibleTypes groups htreeNonempty).2
        ⟨runtimeType, hruntimeTree, rfl⟩
    refine ⟨groups, ?_, ?_⟩
    · unfold selectionSetOutcomes conditionTreeOutcomes
      refine ⟨assignment, hassignment, ?_⟩
      simpa [runtimeGroupSemantics, BooleanEnvironment.concrete,
        BooleanEnvironment.pruningValues, tree] using houtcome
    · simpa [groups, runtimeFieldGroupsFrom, RuntimeCase.fieldGroups, tree] using
        runtimeCaseFieldGroups_representRuntimeGroups schema variableValues parentType
          runtimeType inheritedBooleanCondition selectionSet hinherited hincludes
  · intro groups hgroups
    unfold selectionSetOutcomes conditionTreeOutcomes at hgroups
    rcases hgroups with ⟨assignment, hassignment, houtcome⟩
    have houtcome' :
        CaseCursor.ContextOutcome runtimeGroupSemantics schema assignment
          (BooleanEnvironment.concrete variableValues) inheritedBooleanCondition []
          (.ofConditionTree tree) tree.condition.possibleTypes groups := by
      simpa [runtimeGroupSemantics, BooleanEnvironment.concrete,
        BooleanEnvironment.pruningValues, tree] using houtcome
    rcases (contextOutcome_runtimeGroupSemantics_iff_runtimeType assignment
        variableValues hassignment inheritedBooleanCondition []
        (.ofConditionTree tree) tree.condition.possibleTypes groups
        htreeNonempty).1 houtcome' with
      ⟨runtimeType, hruntimeTree, hequal⟩
    have hincludes : schema.typeIncludesObject parentType runtimeType := by
      unfold Schema.typeIncludesObject
      rw [← htreePossibleTypes]
      exact hruntimeTree
    refine ⟨runtimeType, hincludes, ?_⟩
    rw [← hequal]
    simpa [runtimeFieldGroupsFrom, RuntimeCase.fieldGroups, tree] using
      runtimeCaseFieldGroups_representRuntimeGroups schema variableValues parentType
        runtimeType inheritedBooleanCondition selectionSet hinherited hincludes

end ExactCases
end TreeSummary
end GraphQL
