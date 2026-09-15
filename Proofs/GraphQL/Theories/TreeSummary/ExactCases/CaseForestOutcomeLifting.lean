import Proofs.GraphQL.Theories.TreeSummary.ExactCases.CaseForestOptimality
import Proofs.GraphQL.Theories.TreeSummary.ExactCases.CaseForestRuntimeCases
import Proofs.GraphQL.Theories.TreeSummary.ExactCases.RuntimeCases

/-! The concrete-environment lifting from the batched proof relation to the public
incremental-cursor outcome model. -/

namespace GraphQL
namespace TreeSummary
namespace ExactCases

open GraphQL.ConditionTree
open GraphQL.ConditionTree.Termination
open GraphQL.Execution
open _root_.GraphQL.TreeSummary.Measure
open _root_.GraphQL.TreeSummary.ExactCases.Measure

universe u

namespace CaseForestOutcomeLifting

private theorem branchesTrace_typeFree_of_coherent
    (schema : Schema) (inheritedBooleanCondition : List BooleanLiteral)
    (variableValues : VariableValues) (runtimeType : Name) (parent : Condition)
    (branches : List (Branch Tree)) (hpossible : parent.possibleTypes = [])
    (hcoherent : branchesCoherent schema inheritedBooleanCondition parent branches)
    : (CaseTrace.ofBranches variableValues runtimeType branches).typeConditions = [] := by
  cases branches with
  | nil => simp [CaseTrace.ofBranches, CaseTrace.Trace.empty]
  | cons branch rest =>
      rw [branchesCoherent] at hcoherent
      cases hcondition : branch.condition with
      | typeCondition typeName =>
          unfold conditionForBranch? at hcoherent
          simp [hcondition, hpossible, intersectPossibleTypes] at hcoherent
      | booleanLiteral literal =>
          have hbodyPossible : branch.body.condition.possibleTypes = [] := by
            have hedge := hcoherent.1
            rw [hcondition] at hedge
            simp only [conditionForBranch?] at hedge
            cases hfirst
                  : canonicalBooleanCondition (parent.booleanCondition ++ [literal]) with
            | none => simp [hfirst] at hedge
            | some candidate =>
                cases hsecond
                      : canonicalBooleanCondition
                          (inheritedBooleanCondition
                            ++ candidate.filter
                                fun item =>
                                  !decide (item ∈ inheritedBooleanCondition)) with
                | none => simp [hfirst, hsecond] at hedge
                | some global =>
                    simp [hfirst, hsecond] at hedge
                    exact (congrArg
                      (fun condition : Condition => condition.possibleTypes)
                      hedge).symm.trans hpossible
          have hbody := branchesTrace_typeFree_of_coherent schema
            inheritedBooleanCondition variableValues runtimeType
            branch.body.condition branch.body.branches hbodyPossible
            (by simpa [Tree.BranchesCoherent] using hcoherent.2.1)
          have hrest := branchesTrace_typeFree_of_coherent schema
            inheritedBooleanCondition variableValues runtimeType parent rest hpossible
            hcoherent.2.2
          by_cases hselected :
              CaseTrace.branchSelected variableValues runtimeType branch = true
          · simp [CaseTrace.ofBranches, CaseTrace.branchObservation, hcondition,
              CaseTrace.ofTree, CaseTrace.Trace.append, hselected, hbody, hrest]
          · simp [CaseTrace.ofBranches, CaseTrace.branchObservation, hcondition,
              CaseTrace.Trace.append, CaseTrace.Trace.empty, hselected, hrest]
termination_by (branchNodeConditions branches).length
decreasing_by
  all_goals subst branches
  all_goals simp [branchNodeConditions, Tree.nodeConditions]
  all_goals omega

private theorem treeTrace_typeFree_of_coherent
    (schema : Schema) (inheritedBooleanCondition : List BooleanLiteral)
    (variableValues : VariableValues) (runtimeType : Name) (tree : Tree)
    (hpossible : tree.condition.possibleTypes = [])
    (hcoherent : tree.BranchesCoherent schema inheritedBooleanCondition)
    : (CaseTrace.ofTree variableValues runtimeType tree).typeConditions = [] := by
  simp only [CaseTrace.ofTree, CaseTrace.Trace.append, List.nil_append]
  exact branchesTrace_typeFree_of_coherent schema inheritedBooleanCondition
    variableValues runtimeType tree.condition tree.branches hpossible
    (by simpa [Tree.BranchesCoherent] using hcoherent)

private theorem forestTrace_ofConditionTree
    (variableValues : VariableValues) (runtimeType : Name) (tree : Tree)
    : CaseTrace.ofForest variableValues runtimeType (.ofConditionTree tree)
      = CaseTrace.ofTree variableValues runtimeType tree := by
  change (CaseTrace.ofTree variableValues runtimeType tree).append
      CaseTrace.Trace.empty = CaseTrace.ofTree variableValues runtimeType tree
  exact CaseTrace.Trace.append_empty _

private theorem cursorTrace_ofConditionTree
    (variableValues : VariableValues) (runtimeType : Name) (tree : Tree)
    : CaseTrace.withCaseCondition []
        (CaseTrace.ofCursor variableValues runtimeType (.ofConditionTree tree))
      = CaseTrace.ofTree variableValues runtimeType tree := by
  simp [CaseTrace.withCaseCondition, CaseTrace.ofCursor,
    CaseCursor.ofConditionTree, CaseCursor.namedFields, CaseTrace.ofTree]

private theorem mem_scope_of_mem_typeRegions
    (forest : CaseForest) (scope region : PossibleTypeRegion)
    (hregion : region ∈ forest.typeRegions scope)
    (runtimeType : Name) (hruntime : runtimeType ∈ region)
    : runtimeType ∈ scope := by
  exact ((possibleTypeRegions_exact scope forest.typeBranchPossibleTypes).1
    region hregion).2 runtimeType hruntime

private theorem typeRegion_ne_nil
    (forest : CaseForest) (scope region : PossibleTypeRegion)
    (hregion : region ∈ forest.typeRegions scope)
    : region ≠ [] := by
  exact ((possibleTypeRegions_exact scope forest.typeBranchPossibleTypes).1
    region hregion).1

private theorem forestOutcome_to_runtime
    {semantics : OutcomeSemantics.{u}} {schema : Schema}
    {inheritedBooleanCondition : List BooleanLiteral}
    {forest : CaseForest} {possibleTypes : PossibleTypeRegion}
    {variableValues fixedVariableValues : VariableValues}
    {outcome : semantics.Summary}
    (houtcome
      : CaseForestProof.ContextOutcome semantics schema
          inheritedBooleanCondition forest possibleTypes variableValues
          fixedVariableValues outcome)
    (hnonempty : possibleTypes ≠ [])
    : ∃ runtimeType,
        runtimeType ∈ possibleTypes
        ∧ CaseForestProof.ContextFieldGroupsOutcome semantics schema
            (CaseForestRuntimeCase.fieldGroups "" inheritedBooleanCondition forest
              possibleTypes runtimeType variableValues)
            variableValues fixedVariableValues outcome := by
  cases houtcome with
  | booleanFrontier inherited forest possibleTypes variableValues
      fixedVariableValues outcome hbranches htypes hnext =>
      obtain ⟨runtimeType, hruntime, hgroups⟩ :=
        forestOutcome_to_runtime hnext hnonempty
      refine ⟨runtimeType, hruntime, ?_⟩
      have hempty : forest.typeBranchPossibleTypes = [] :=
        List.isEmpty_iff.mp htypes
      have hchosen :
          CaseForestRuntimeCase.chooseTypeRegion runtimeType possibleTypes
              (forest.typeRegions possibleTypes) = possibleTypes := by
        exact CaseForestRuntimeCase.chooseTypeRegion_eq_scope_of_no_typeBranches
          forest possibleTypes runtimeType hempty
      unfold CaseForestRuntimeCase.fieldGroups
      rw [CaseForestRuntimeCase.resolve.eq_1]
      simp only [hbranches, dite_true]
      rw [hchosen]
      exact hgroups
  | noRegion inherited forest possibleTypes variableValues fixedVariableValues
      hbranches _htypes hregions =>
      obtain ⟨runtimeType, hruntime⟩ :=
        List.exists_mem_of_ne_nil possibleTypes hnonempty
      have hchosen := CaseForestRuntimeCase.chooseTypeRegion_mem forest possibleTypes
        runtimeType hruntime
      rw [hregions] at hchosen
      exact False.elim (by simpa using hchosen.1)
  | region inherited forest possibleTypes variableValues fixedVariableValues
      selectedRegion outcome hbranches _htypes hregion hnext =>
      have hselectedNonempty := typeRegion_ne_nil forest possibleTypes selectedRegion
        hregion
      obtain ⟨runtimeType, hruntime, hgroups⟩ :=
        forestOutcome_to_runtime hnext hselectedNonempty
      have hscope := mem_scope_of_mem_typeRegions forest possibleTypes selectedRegion
        hregion runtimeType hruntime
      refine ⟨runtimeType, hscope, ?_⟩
      have hchosen := CaseForestRuntimeCase.chooseTypeRegion_eq_of_mem forest
        possibleTypes runtimeType hscope selectedRegion hregion hruntime
      unfold CaseForestRuntimeCase.fieldGroups
      rw [CaseForestRuntimeCase.resolve.eq_1]
      simp only [hbranches, dite_true]
      rw [hchosen]
      exact hgroups
  | fields inherited forest possibleTypes variableValues fixedVariableValues outcome
      hbranches hgroups =>
      obtain ⟨runtimeType, hruntime⟩ :=
        List.exists_mem_of_ne_nil possibleTypes hnonempty
      refine ⟨runtimeType, hruntime, ?_⟩
      unfold CaseForestRuntimeCase.fieldGroups
      rw [CaseForestRuntimeCase.resolve.eq_1]
      simp only [hbranches]
      exact hgroups
termination_by
  (caseForestResponseDepth forest, caseForestUnresolvedCount forest, 3, 0)
decreasing_by
  all_goals
    apply _root_.GraphQL.TreeSummary.Measure.quadruple_lt_of_depth_le_of_control_lt
    · exact Measure.resolveBranches_responseDepth_le _ _ _
    · exact Measure.resolveBranches_unresolvedCount_lt _ _ _ (by assumption)

private theorem forestOutcome_of_runtime
    {semantics : OutcomeSemantics.{u}} (schema : Schema)
    (inheritedBooleanCondition : List BooleanLiteral)
    (forest : CaseForest) (possibleTypes : PossibleTypeRegion)
    (runtimeType : Name) (variableValues fixedVariableValues : VariableValues)
    (outcome : semantics.Summary)
    (hruntime : runtimeType ∈ possibleTypes)
    (hgroups
      : CaseForestProof.ContextFieldGroupsOutcome semantics schema
          (CaseForestRuntimeCase.fieldGroups "" inheritedBooleanCondition forest
            possibleTypes runtimeType variableValues)
          variableValues fixedVariableValues outcome)
    : CaseForestProof.ContextOutcome semantics schema inheritedBooleanCondition forest
        possibleTypes variableValues fixedVariableValues outcome := by
  cases hbranches : forest.hasUnresolvedBranches with
  | false =>
      apply CaseForestProof.ContextOutcome.fields inheritedBooleanCondition forest
        possibleTypes variableValues fixedVariableValues outcome hbranches
      unfold CaseForestRuntimeCase.fieldGroups at hgroups
      rw [CaseForestRuntimeCase.resolve.eq_1] at hgroups
      simp only [hbranches] at hgroups
      exact hgroups
  | true =>
      cases htypes : forest.typeBranchPossibleTypes.isEmpty with
      | true =>
          apply CaseForestProof.ContextOutcome.booleanFrontier inheritedBooleanCondition
            forest possibleTypes variableValues fixedVariableValues outcome hbranches
            htypes
          apply forestOutcome_of_runtime schema
            (CaseForest.extendBooleanCondition inheritedBooleanCondition
              forest.booleanVariables variableValues)
            (forest.resolveBranches possibleTypes variableValues) possibleTypes
            runtimeType variableValues fixedVariableValues outcome hruntime
          unfold CaseForestRuntimeCase.fieldGroups at hgroups
          rw [CaseForestRuntimeCase.resolve.eq_1] at hgroups
          simp only [hbranches, dite_true] at hgroups
          have hempty : forest.typeBranchPossibleTypes = [] :=
            List.isEmpty_iff.mp htypes
          have hchosen :
              CaseForestRuntimeCase.chooseTypeRegion runtimeType possibleTypes
                  (forest.typeRegions possibleTypes) = possibleTypes := by
            exact CaseForestRuntimeCase.chooseTypeRegion_eq_scope_of_no_typeBranches
              forest possibleTypes runtimeType hempty
          rw [hchosen] at hgroups
          exact hgroups
      | false =>
          let region := CaseForestRuntimeCase.chooseTypeRegion runtimeType possibleTypes
            (forest.typeRegions possibleTypes)
          have hregion := CaseForestRuntimeCase.chooseTypeRegion_mem forest possibleTypes
            runtimeType hruntime
          apply CaseForestProof.ContextOutcome.region inheritedBooleanCondition forest
            possibleTypes variableValues fixedVariableValues region outcome hbranches htypes
            hregion.1
          apply forestOutcome_of_runtime schema
            (CaseForest.extendBooleanCondition inheritedBooleanCondition
              forest.booleanVariables variableValues)
            (forest.resolveBranches region variableValues) region runtimeType variableValues
            fixedVariableValues outcome hregion.2
          unfold CaseForestRuntimeCase.fieldGroups at hgroups
          rw [CaseForestRuntimeCase.resolve.eq_1] at hgroups
          simp only [hbranches, dite_true] at hgroups
          exact hgroups
termination_by
  (caseForestResponseDepth forest, caseForestUnresolvedCount forest, 3, 0)
decreasing_by
  all_goals
    apply _root_.GraphQL.TreeSummary.Measure.quadruple_lt_of_depth_le_of_control_lt
    · exact Measure.resolveBranches_responseDepth_le _ variableValues forest
    · exact Measure.resolveBranches_unresolvedCount_lt _ variableValues forest hbranches

theorem forestOutcome_iff_runtime
    {semantics : OutcomeSemantics.{u}} (schema : Schema)
    (inheritedBooleanCondition : List BooleanLiteral)
    (forest : CaseForest) (possibleTypes : PossibleTypeRegion)
    (variableValues fixedVariableValues : VariableValues)
    (outcome : semantics.Summary) (hnonempty : possibleTypes ≠ [])
    : CaseForestProof.ContextOutcome semantics schema inheritedBooleanCondition forest
        possibleTypes variableValues fixedVariableValues outcome
      ↔ ∃ runtimeType,
          runtimeType ∈ possibleTypes
          ∧ CaseForestProof.ContextFieldGroupsOutcome semantics schema
              (CaseForestRuntimeCase.fieldGroups "" inheritedBooleanCondition forest
                possibleTypes runtimeType variableValues)
              variableValues fixedVariableValues outcome := by
  constructor
  · exact fun h => forestOutcome_to_runtime h hnonempty
  · rintro ⟨runtimeType, hruntime, hgroups⟩
    exact forestOutcome_of_runtime schema inheritedBooleanCondition forest possibleTypes
      runtimeType variableValues fixedVariableValues outcome hruntime hgroups

private theorem forestOutcome_to_typeFree
    {semantics : OutcomeSemantics.{u}} {schema : Schema}
    {inheritedBooleanCondition : List BooleanLiteral}
    {forest : CaseForest} {possibleTypes : PossibleTypeRegion}
    {runtimeType : Name} {variableValues fixedVariableValues : VariableValues}
    {outcome : semantics.Summary}
    (houtcome
      : CaseForestProof.ContextOutcome semantics schema
          inheritedBooleanCondition forest possibleTypes variableValues
          fixedVariableValues outcome)
    (htypes : (CaseTrace.ofForest variableValues runtimeType forest).typeConditions = [])
    : CaseForestProof.ContextFieldGroupsOutcome semantics schema
        (CaseForestRuntimeCase.fieldGroups "" inheritedBooleanCondition forest
          possibleTypes runtimeType variableValues)
        variableValues fixedVariableValues outcome := by
  cases houtcome with
  | booleanFrontier inherited forest possibleTypes variableValues
      fixedVariableValues outcome hbranches _htypes hnext =>
      have hstep := CaseTrace.resolveBranches_typeFree forest possibleTypes runtimeType
        variableValues htypes
      have hgroups := forestOutcome_to_typeFree hnext hstep.2.2.1
      unfold CaseForestRuntimeCase.fieldGroups
      rw [CaseForestRuntimeCase.resolve.eq_1]
      simp only [hbranches, dite_true]
      have hchosen :
          CaseForestRuntimeCase.chooseTypeRegion runtimeType possibleTypes
              (forest.typeRegions possibleTypes) = possibleTypes := by
        exact CaseForestRuntimeCase.chooseTypeRegion_eq_scope_of_no_typeBranches
          forest possibleTypes runtimeType hstep.1
      rw [hchosen]
      exact hgroups
  | noRegion inherited forest possibleTypes variableValues fixedVariableValues
      _hbranches htypesFrontier _hregions =>
      have hstep := CaseTrace.resolveBranches_typeFree forest possibleTypes runtimeType
        variableValues htypes
      rw [hstep.1] at htypesFrontier
      contradiction
  | region inherited forest possibleTypes variableValues fixedVariableValues
      selectedRegion outcome _hbranches htypesFrontier _hregion _hnext =>
      have hstep := CaseTrace.resolveBranches_typeFree forest possibleTypes runtimeType
        variableValues htypes
      rw [hstep.1] at htypesFrontier
      contradiction
  | fields inherited forest possibleTypes variableValues fixedVariableValues outcome
      hbranches hgroups =>
      unfold CaseForestRuntimeCase.fieldGroups
      rw [CaseForestRuntimeCase.resolve.eq_1]
      simp only [hbranches]
      exact hgroups
termination_by
  (caseForestResponseDepth forest, caseForestUnresolvedCount forest, 3, 0)
decreasing_by
  apply _root_.GraphQL.TreeSummary.Measure.quadruple_lt_of_depth_le_of_control_lt
  · exact Measure.resolveBranches_responseDepth_le _ _ _
  · exact Measure.resolveBranches_unresolvedCount_lt _ _ _ (by assumption)

private theorem forestOutcome_of_typeFree
    {semantics : OutcomeSemantics.{u}} (schema : Schema)
    (inheritedBooleanCondition : List BooleanLiteral)
    (forest : CaseForest) (possibleTypes : PossibleTypeRegion)
    (runtimeType : Name) (variableValues fixedVariableValues : VariableValues)
    (outcome : semantics.Summary)
    (htypes : (CaseTrace.ofForest variableValues runtimeType forest).typeConditions = [])
    (hgroups
      : CaseForestProof.ContextFieldGroupsOutcome semantics schema
          (CaseForestRuntimeCase.fieldGroups "" inheritedBooleanCondition forest
            possibleTypes runtimeType variableValues)
          variableValues fixedVariableValues outcome)
    : CaseForestProof.ContextOutcome semantics schema inheritedBooleanCondition forest
        possibleTypes variableValues fixedVariableValues outcome := by
  cases hbranches : forest.hasUnresolvedBranches with
  | false =>
      apply CaseForestProof.ContextOutcome.fields inheritedBooleanCondition forest
        possibleTypes variableValues fixedVariableValues outcome hbranches
      unfold CaseForestRuntimeCase.fieldGroups at hgroups
      rw [CaseForestRuntimeCase.resolve.eq_1] at hgroups
      simp only [hbranches] at hgroups
      exact hgroups
  | true =>
      have hstep := CaseTrace.resolveBranches_typeFree forest possibleTypes runtimeType
        variableValues htypes
      apply CaseForestProof.ContextOutcome.booleanFrontier inheritedBooleanCondition
        forest possibleTypes variableValues fixedVariableValues outcome hbranches
        (by simp [hstep.1])
      apply forestOutcome_of_typeFree schema
        (CaseForest.extendBooleanCondition inheritedBooleanCondition
          forest.booleanVariables variableValues)
        (forest.resolveBranches possibleTypes variableValues) possibleTypes runtimeType
        variableValues fixedVariableValues outcome hstep.2.2.1
      unfold CaseForestRuntimeCase.fieldGroups at hgroups
      rw [CaseForestRuntimeCase.resolve.eq_1] at hgroups
      simp only [hbranches, dite_true] at hgroups
      have hchosen :
          CaseForestRuntimeCase.chooseTypeRegion runtimeType possibleTypes
              (forest.typeRegions possibleTypes) = possibleTypes := by
        exact CaseForestRuntimeCase.chooseTypeRegion_eq_scope_of_no_typeBranches
          forest possibleTypes runtimeType hstep.1
      rw [hchosen] at hgroups
      exact hgroups
termination_by
  (caseForestResponseDepth forest, caseForestUnresolvedCount forest, 3, 0)
decreasing_by
  apply _root_.GraphQL.TreeSummary.Measure.quadruple_lt_of_depth_le_of_control_lt
  · exact Measure.resolveBranches_responseDepth_le _ _ _
  · exact Measure.resolveBranches_unresolvedCount_lt _ _ _ (by assumption)

private theorem forestOutcome_iff_typeFree
    {semantics : OutcomeSemantics.{u}} (schema : Schema)
    (inheritedBooleanCondition : List BooleanLiteral)
    (forest : CaseForest) (possibleTypes : PossibleTypeRegion)
    (runtimeType : Name) (variableValues fixedVariableValues : VariableValues)
    (outcome : semantics.Summary)
    (htypes : (CaseTrace.ofForest variableValues runtimeType forest).typeConditions = [])
    : CaseForestProof.ContextOutcome semantics schema inheritedBooleanCondition forest
        possibleTypes variableValues fixedVariableValues outcome
      ↔ CaseForestProof.ContextFieldGroupsOutcome semantics schema
          (CaseForestRuntimeCase.fieldGroups "" inheritedBooleanCondition forest
            possibleTypes runtimeType variableValues)
          variableValues fixedVariableValues outcome := by
  constructor
  · exact fun h => forestOutcome_to_typeFree h htypes
  · exact fun h => forestOutcome_of_typeFree schema inheritedBooleanCondition forest
      possibleTypes runtimeType variableValues fixedVariableValues outcome htypes h

private def cursorFieldGroups
    (inheritedBooleanCondition caseCondition : List BooleanLiteral) (cursor : CaseCursor)
    (possibleTypes : PossibleTypeRegion) (runtimeType : Name)
    (variableValues : VariableValues)
    : List CollectedFieldGroup :=
  let resolved :=
    RuntimeCase.resolve inheritedBooleanCondition caseCondition cursor
      possibleTypes runtimeType variableValues
  resolved.cursor.fieldGroups resolved.inheritedBooleanCondition resolved.possibleTypes

private theorem unresolvedBranchesCount_append (left right : List (Branch Tree))
    : unresolvedBranchesCount (left ++ right)
      = unresolvedBranchesCount left + unresolvedBranchesCount right := by
  induction left with
  | nil => simp [unresolvedBranchesCount]
  | cons branch rest ih => simp [unresolvedBranchesCount, ih, Nat.add_assoc]

private theorem cursorSkip_unresolved_lt (cursor : CaseCursor)
    (branch : Branch Tree) (rest : List (Branch Tree))
    (hbranches : cursor.pendingBranches = branch :: rest)
    : caseCursorUnresolvedCount (cursor.skipBranch rest)
      < caseCursorUnresolvedCount cursor := by
  simp [caseCursorUnresolvedCount, CaseCursor.skipBranch, hbranches,
    unresolvedBranchesCount]
  omega

private theorem cursorSelect_unresolved_lt (cursor : CaseCursor)
    (branch : Branch Tree) (rest : List (Branch Tree))
    (hbranches : cursor.pendingBranches = branch :: rest)
    : caseCursorUnresolvedCount (cursor.selectBranch branch.body rest)
      < caseCursorUnresolvedCount cursor := by
  simp [caseCursorUnresolvedCount, CaseCursor.selectBranch, hbranches,
    unresolvedBranchesCount_append, unresolvedBranchesCount,
    unresolvedBranchCount]

private theorem cursorBoolean_unresolved_lt (cursor : CaseCursor)
    (branch : Branch Tree) (rest : List (Branch Tree))
    (hbranches : cursor.pendingBranches = branch :: rest)
    (literal : BooleanLiteral) (value : Bool)
    : caseCursorUnresolvedCount
        (cursor.resolveBooleanBranch branch.body rest literal value)
      < caseCursorUnresolvedCount cursor := by
  unfold CaseCursor.resolveBooleanBranch
  split
  · exact cursorSelect_unresolved_lt cursor branch rest hbranches
  · exact cursorSkip_unresolved_lt cursor branch rest hbranches

private theorem cursorTrace_resolveBoolean
    (variableValues : VariableValues) (runtimeType : Name)
    (caseCondition : List BooleanLiteral) (cursor : CaseCursor)
    (branch : Branch Tree) (rest : List (Branch Tree)) (literal : BooleanLiteral)
    (hbranches : cursor.pendingBranches = branch :: rest)
    (hcondition : branch.condition = .booleanLiteral literal)
    : let value := CaseForest.booleanValue variableValues literal.variableName
      CaseTrace.withCaseCondition caseCondition
        (CaseTrace.ofCursor variableValues runtimeType cursor)
      = CaseTrace.withCaseCondition
          ((if value then
              .positive literal.variableName
            else
              .negative literal.variableName)
            :: caseCondition)
          (CaseTrace.ofCursor variableValues runtimeType
            (cursor.resolveBooleanBranch branch.body rest literal value)) := by
  cases literal with
  | positive variableName =>
      cases hvalue : CaseForest.booleanValue variableValues variableName <;>
        simp [CaseTrace.withCaseCondition, CaseTrace.ofCursor, CaseTrace.ofTree,
          CaseTrace.ofBranches, CaseTrace.ofBranches_append,
          CaseTrace.Trace.append, CaseTrace.Trace.empty,
          CaseTrace.branchObservation, CaseTrace.branchSelected,
          CaseTrace.selectedLiteral, CaseCursor.resolveBooleanBranch,
          CaseCursor.selectBranch, CaseCursor.skipBranch, CaseCursor.namedFields,
          hbranches, hcondition, hvalue, BooleanLiteral.requiredValue,
          BooleanLiteral.variableName, List.reverse_cons, List.append_assoc]

  | negative variableName =>
      cases hvalue : CaseForest.booleanValue variableValues variableName <;>
        simp [CaseTrace.withCaseCondition, CaseTrace.ofCursor, CaseTrace.ofTree,
          CaseTrace.ofBranches, CaseTrace.ofBranches_append,
          CaseTrace.Trace.append, CaseTrace.Trace.empty,
          CaseTrace.branchObservation, CaseTrace.branchSelected,
          CaseTrace.selectedLiteral, CaseCursor.resolveBooleanBranch,
          CaseCursor.selectBranch, CaseCursor.skipBranch, CaseCursor.namedFields,
          hbranches, hcondition, hvalue, BooleanLiteral.requiredValue,
          BooleanLiteral.variableName, List.reverse_cons, List.append_assoc]

private theorem cursorFieldGroups_eq_trace_of_typeFree
    (inheritedBooleanCondition caseCondition : List BooleanLiteral)
    (cursor : CaseCursor) (possibleTypes : PossibleTypeRegion)
    (runtimeType : Name) (variableValues : VariableValues)
    (htypes
      : (CaseTrace.withCaseCondition caseCondition
          (CaseTrace.ofCursor variableValues runtimeType cursor)).typeConditions
        = [])
    : cursorFieldGroups inheritedBooleanCondition caseCondition cursor possibleTypes
        runtimeType variableValues
      = CaseTrace.fieldGroups inheritedBooleanCondition possibleTypes runtimeType
          (CaseTrace.withCaseCondition caseCondition
            (CaseTrace.ofCursor variableValues runtimeType cursor)) := by
  cases hbranches : cursor.pendingBranches with
  | nil =>
      unfold cursorFieldGroups
      rw [RuntimeCase.resolve_nil inheritedBooleanCondition caseCondition cursor
        possibleTypes runtimeType variableValues hbranches]
      simp [CaseTrace.fieldGroups, CaseTrace.inheritedBooleanCondition,
        CaseTrace.possibleTypes, CaseTrace.withCaseCondition, CaseTrace.ofCursor,
        hbranches, CaseTrace.ofBranches, CaseTrace.Trace.append,
        CaseTrace.Trace.empty, possibleTypeMembershipClass]
      rw [List.filter_eq_self.mpr (fun _ _ => by simp)]
      rfl
  | cons branch rest =>
      cases hcondition : branch.condition with
      | typeCondition typeName =>
          simp [CaseTrace.withCaseCondition, CaseTrace.ofCursor,
            CaseTrace.ofBranches, CaseTrace.branchObservation,
            CaseTrace.Trace.append, hbranches, hcondition] at htypes
      | booleanLiteral literal =>
          let value := CaseForest.booleanValue variableValues literal.variableName
          let nextCase :=
            (if value then .positive literal.variableName else
              .negative literal.variableName) :: caseCondition
          let nextCursor := cursor.resolveBooleanBranch branch.body rest literal value
          have htrace := cursorTrace_resolveBoolean variableValues runtimeType
            caseCondition cursor branch rest literal hbranches hcondition
          have hnextTypes :
              (CaseTrace.withCaseCondition nextCase
                (CaseTrace.ofCursor variableValues runtimeType nextCursor)).typeConditions =
                [] := by
            rw [← htrace]
            exact htypes
          have ih := cursorFieldGroups_eq_trace_of_typeFree
            inheritedBooleanCondition nextCase nextCursor possibleTypes runtimeType
            variableValues hnextTypes
          have hfieldGroups :
              cursorFieldGroups inheritedBooleanCondition caseCondition cursor
                  possibleTypes runtimeType variableValues =
                cursorFieldGroups inheritedBooleanCondition nextCase nextCursor
                  possibleTypes runtimeType variableValues := by
            unfold cursorFieldGroups
            rw [RuntimeCase.resolve_booleanLiteral inheritedBooleanCondition caseCondition
              cursor possibleTypes runtimeType variableValues branch rest literal hbranches
              hcondition]
            rfl
          rw [hfieldGroups, ih, htrace]
termination_by caseCursorUnresolvedCount cursor
decreasing_by
  all_goals apply cursorBoolean_unresolved_lt <;> assumption

private theorem cursorRegion_mem_scope
    (scope allowed region : PossibleTypeRegion)
    (hregion : region ∈ possibleTypeRegions scope [allowed])
    (runtimeType : Name) (hruntime : runtimeType ∈ region)
    : runtimeType ∈ scope :=
  ((possibleTypeRegions_exact scope [allowed]).1 region hregion).2 runtimeType hruntime

private theorem cursorRegion_ne_nil
    (scope allowed region : PossibleTypeRegion)
    (hregion : region ∈ possibleTypeRegions scope [allowed])
    : region ≠ [] :=
  ((possibleTypeRegions_exact scope [allowed]).1 region hregion).1

private theorem cursorOutcome_to_runtime
    {semantics : OutcomeSemantics.{u}} {schema : Schema}
    {assignment : BooleanAssignment}
    {inheritedBooleanCondition caseCondition : List BooleanLiteral}
    {cursor : CaseCursor} {possibleTypes : PossibleTypeRegion}
    {variableValues : VariableValues} {outcome : semantics.Summary}
    (houtcome
      : CaseCursor.ContextOutcome semantics schema assignment
          (.concrete variableValues) inheritedBooleanCondition caseCondition cursor
          possibleTypes outcome)
    (hnonempty : possibleTypes ≠ [])
    : ∃ runtimeType,
        runtimeType ∈ possibleTypes
        ∧ CaseCursor.ContextFieldGroupsOutcome semantics schema assignment
            (.concrete variableValues)
            (cursorFieldGroups inheritedBooleanCondition caseCondition cursor
              possibleTypes runtimeType variableValues)
            outcome := by
  cases houtcome with
  | noTypeRegion assignment inherited caseCondition cursor possibleTypes
      branch rest typeName hbranches hcondition hregions =>
      obtain ⟨runtimeType, hruntime⟩ :=
        List.exists_mem_of_ne_nil possibleTypes hnonempty
      have hchosen := RuntimeCase.chooseTypeRegion_mem possibleTypes
        [branch.body.condition.possibleTypes] runtimeType hruntime
      rw [hregions] at hchosen
      exact False.elim (by simpa using hchosen.1)
  | selectTypeRegion assignment inherited caseCondition cursor possibleTypes
      branch rest typeName region outcome hbranches hcondition hregion hselected hnext =>
      have hregionNonempty := cursorRegion_ne_nil possibleTypes
        branch.body.condition.possibleTypes region hregion
      obtain ⟨runtimeType, hruntime, hgroups⟩ :=
        cursorOutcome_to_runtime hnext hregionNonempty
      have hscope := cursorRegion_mem_scope possibleTypes
        branch.body.condition.possibleTypes region hregion runtimeType hruntime
      refine ⟨runtimeType, hscope, ?_⟩
      have hchosen := RuntimeCase.chooseTypeRegion_eq_of_mem possibleTypes
        [branch.body.condition.possibleTypes] runtimeType hscope region hregion hruntime
      have hfieldGroups :
          cursorFieldGroups inheritedBooleanCondition caseCondition cursor possibleTypes runtimeType
              variableValues =
            cursorFieldGroups inheritedBooleanCondition caseCondition
              (cursor.selectBranch branch.body rest) region runtimeType variableValues := by
        unfold cursorFieldGroups
        rw [RuntimeCase.resolve_typeCondition inheritedBooleanCondition caseCondition
          cursor possibleTypes runtimeType variableValues branch rest typeName hbranches
          hcondition]
        rw [hchosen, hselected]
        simp
      rwa [hfieldGroups]
  | skipTypeRegion assignment inherited caseCondition cursor possibleTypes
      branch rest typeName region outcome hbranches hcondition hregion hskipped hnext =>
      have hregionNonempty := cursorRegion_ne_nil possibleTypes
        branch.body.condition.possibleTypes region hregion
      obtain ⟨runtimeType, hruntime, hgroups⟩ :=
        cursorOutcome_to_runtime hnext hregionNonempty
      have hscope := cursorRegion_mem_scope possibleTypes
        branch.body.condition.possibleTypes region hregion runtimeType hruntime
      refine ⟨runtimeType, hscope, ?_⟩
      have hchosen := RuntimeCase.chooseTypeRegion_eq_of_mem possibleTypes
        [branch.body.condition.possibleTypes] runtimeType hscope region hregion hruntime
      have hfieldGroups :
          cursorFieldGroups inheritedBooleanCondition caseCondition cursor possibleTypes runtimeType
              variableValues =
            cursorFieldGroups inheritedBooleanCondition caseCondition (cursor.skipBranch rest) region
              runtimeType variableValues := by
        unfold cursorFieldGroups
        rw [RuntimeCase.resolve_typeCondition inheritedBooleanCondition caseCondition
          cursor possibleTypes runtimeType variableValues branch rest typeName hbranches
          hcondition]
        rw [hchosen, hskipped]
        simp
      rwa [hfieldGroups]
  | knownBoolean assignment inherited caseCondition cursor possibleTypes
      branch rest literal value outcome hbranches hcondition hstatus hnext =>
      have hvalue
          : value = CaseForest.booleanValue variableValues literal.variableName := by
        rw [CaseCursor.BooleanEnvironment.concrete_statusForVariable] at hstatus
        cases hlookup
              : inputValueBoolean? variableValues (.variable literal.variableName) with
        | none =>
            simpa [hlookup, CaseForest.booleanValue] using hstatus
        | some selected =>
            simpa [hlookup, CaseForest.booleanValue] using hstatus.symm
      obtain ⟨runtimeType, hruntime, hgroups⟩ :=
        cursorOutcome_to_runtime hnext hnonempty
      refine ⟨runtimeType, hruntime, ?_⟩
      have hfieldGroups :
          cursorFieldGroups inheritedBooleanCondition caseCondition cursor possibleTypes runtimeType
              variableValues =
            cursorFieldGroups inheritedBooleanCondition
              ((if value then .positive literal.variableName else
                .negative literal.variableName) :: caseCondition)
              (cursor.resolveBooleanBranch branch.body rest literal value) possibleTypes
              runtimeType variableValues := by
        unfold cursorFieldGroups
        rw [RuntimeCase.resolve_booleanLiteral inheritedBooleanCondition caseCondition
          cursor possibleTypes runtimeType variableValues branch rest literal hbranches
          hcondition]
        unfold CaseForest.booleanValue at hvalue
        rw [← hvalue]
      rwa [hfieldGroups]
  | splitBoolean assignment inherited caseCondition cursor possibleTypes
      branch rest literal outcome hbranches hcondition hstatus hnext =>
      rw [CaseCursor.BooleanEnvironment.concrete_statusForVariable] at hstatus
      cases hlookup : inputValueBoolean? variableValues (.variable literal.variableName) <;>
        simp [hlookup] at hstatus
  | fields assignment inherited caseCondition cursor possibleTypes outcome
      hbranches hgroups =>
      obtain ⟨runtimeType, hruntime⟩ :=
        List.exists_mem_of_ne_nil possibleTypes hnonempty
      refine ⟨runtimeType, hruntime, ?_⟩
      have hfieldGroups :
          cursorFieldGroups inheritedBooleanCondition caseCondition cursor possibleTypes runtimeType
              variableValues =
            cursor.fieldGroups
              (Internal.extendBooleanCondition inheritedBooleanCondition caseCondition)
              possibleTypes := by
        unfold cursorFieldGroups
        rw [RuntimeCase.resolve_nil inheritedBooleanCondition caseCondition cursor
          possibleTypes runtimeType variableValues hbranches]
      rwa [hfieldGroups]
termination_by caseCursorUnresolvedCount cursor
decreasing_by
  all_goals first
    | apply cursorSelect_unresolved_lt <;> assumption
    | apply cursorSkip_unresolved_lt <;> assumption
    | apply cursorBoolean_unresolved_lt <;> assumption

private theorem cursorOutcome_of_runtime
    {semantics : OutcomeSemantics.{u}} (schema : Schema)
    (assignment : BooleanAssignment)
    (inheritedBooleanCondition caseCondition : List BooleanLiteral)
    (cursor : CaseCursor) (possibleTypes : PossibleTypeRegion)
    (runtimeType : Name) (variableValues : VariableValues)
    (outcome : semantics.Summary) (hruntime : runtimeType ∈ possibleTypes)
    (hgroups
      : CaseCursor.ContextFieldGroupsOutcome semantics schema assignment
          (.concrete variableValues)
          (cursorFieldGroups inheritedBooleanCondition caseCondition cursor possibleTypes
            runtimeType variableValues)
          outcome)
    : CaseCursor.ContextOutcome semantics schema assignment (.concrete variableValues)
        inheritedBooleanCondition caseCondition cursor possibleTypes outcome := by
  cases hbranches : cursor.pendingBranches with
  | nil =>
      apply CaseCursor.ContextOutcome.fields assignment (.concrete variableValues)
        inheritedBooleanCondition caseCondition cursor possibleTypes outcome hbranches
      have hfieldGroups :
          cursorFieldGroups inheritedBooleanCondition caseCondition cursor possibleTypes
              runtimeType variableValues =
            cursor.fieldGroups
              (Internal.extendBooleanCondition inheritedBooleanCondition caseCondition)
              possibleTypes := by
        unfold cursorFieldGroups
        rw [RuntimeCase.resolve_nil inheritedBooleanCondition caseCondition cursor
          possibleTypes runtimeType variableValues hbranches]
      rwa [← hfieldGroups]
  | cons branch rest =>
      cases hcondition : branch.condition with
      | typeCondition typeName =>
          let region := RuntimeCase.chooseTypeRegion runtimeType possibleTypes
            (possibleTypeRegions possibleTypes [branch.body.condition.possibleTypes])
          have hregion := RuntimeCase.chooseTypeRegion_mem possibleTypes
            [branch.body.condition.possibleTypes] runtimeType hruntime
          cases hselected
                : possibleTypesSubset region branch.body.condition.possibleTypes with
          | false =>
              apply CaseCursor.ContextOutcome.skipTypeRegion assignment
                (.concrete variableValues) inheritedBooleanCondition caseCondition cursor
                possibleTypes branch rest typeName region outcome hbranches hcondition
                hregion.1 hselected
              apply cursorOutcome_of_runtime schema assignment inheritedBooleanCondition
                caseCondition (cursor.skipBranch rest) region runtimeType variableValues
                outcome hregion.2
              have hfieldGroups :
                  cursorFieldGroups inheritedBooleanCondition caseCondition cursor
                      possibleTypes runtimeType variableValues =
                    cursorFieldGroups inheritedBooleanCondition caseCondition
                      (cursor.skipBranch rest) region runtimeType variableValues := by
                unfold cursorFieldGroups
                rw [RuntimeCase.resolve_typeCondition inheritedBooleanCondition
                  caseCondition cursor possibleTypes runtimeType variableValues branch rest
                  typeName hbranches hcondition]
                simp [region, hselected]
              rwa [← hfieldGroups]
          | true =>
              apply CaseCursor.ContextOutcome.selectTypeRegion assignment
                (.concrete variableValues) inheritedBooleanCondition caseCondition cursor
                possibleTypes branch rest typeName region outcome hbranches hcondition
                hregion.1 hselected
              apply cursorOutcome_of_runtime schema assignment inheritedBooleanCondition
                caseCondition (cursor.selectBranch branch.body rest) region runtimeType
                variableValues outcome hregion.2
              have hfieldGroups :
                  cursorFieldGroups inheritedBooleanCondition caseCondition cursor
                      possibleTypes runtimeType variableValues =
                    cursorFieldGroups inheritedBooleanCondition caseCondition
                      (cursor.selectBranch branch.body rest) region runtimeType
                      variableValues := by
                unfold cursorFieldGroups
                rw [RuntimeCase.resolve_typeCondition inheritedBooleanCondition
                  caseCondition cursor possibleTypes runtimeType variableValues branch rest
                  typeName hbranches hcondition]
                simp [region, hselected]
              rwa [← hfieldGroups]
      | booleanLiteral literal =>
          let value := CaseForest.booleanValue variableValues literal.variableName
          have hstatus :
              (CaseCursor.BooleanEnvironment.concrete variableValues).statusForVariable
                literal.variableName = some value := by
            rw [CaseCursor.BooleanEnvironment.concrete_statusForVariable]
            cases hlookup : inputValueBoolean? variableValues
                (.variable literal.variableName) <;>
              simp [value, CaseForest.booleanValue, hlookup]
          apply CaseCursor.ContextOutcome.knownBoolean assignment
            (.concrete variableValues) inheritedBooleanCondition caseCondition cursor
            possibleTypes branch rest literal value outcome hbranches hcondition hstatus
          apply cursorOutcome_of_runtime schema assignment inheritedBooleanCondition
            ((if value then .positive literal.variableName else
              .negative literal.variableName) :: caseCondition)
            (cursor.resolveBooleanBranch branch.body rest literal value) possibleTypes
            runtimeType variableValues outcome hruntime
          have hfieldGroups :
              cursorFieldGroups inheritedBooleanCondition caseCondition cursor
                  possibleTypes runtimeType variableValues =
                cursorFieldGroups inheritedBooleanCondition
                  ((if value then .positive literal.variableName else
                    .negative literal.variableName) :: caseCondition)
                  (cursor.resolveBooleanBranch branch.body rest literal value)
                  possibleTypes runtimeType variableValues := by
            unfold cursorFieldGroups
            rw [RuntimeCase.resolve_booleanLiteral inheritedBooleanCondition caseCondition
              cursor possibleTypes runtimeType variableValues branch rest literal hbranches
              hcondition]
            rfl
          rwa [← hfieldGroups]
termination_by caseCursorUnresolvedCount cursor
decreasing_by
  all_goals first
    | apply cursorSelect_unresolved_lt <;> assumption
    | apply cursorSkip_unresolved_lt <;> assumption
    | apply cursorBoolean_unresolved_lt <;> assumption

theorem cursorOutcome_iff_runtime
    {semantics : OutcomeSemantics.{u}} (schema : Schema)
    (assignment : BooleanAssignment)
    (inheritedBooleanCondition caseCondition : List BooleanLiteral)
    (cursor : CaseCursor) (possibleTypes : PossibleTypeRegion)
    (variableValues : VariableValues) (outcome : semantics.Summary)
    (hnonempty : possibleTypes ≠ [])
    : CaseCursor.ContextOutcome semantics schema assignment (.concrete variableValues)
        inheritedBooleanCondition caseCondition cursor possibleTypes outcome
      ↔ ∃ runtimeType,
          runtimeType ∈ possibleTypes
          ∧ CaseCursor.ContextFieldGroupsOutcome semantics schema assignment
              (.concrete variableValues)
              (cursorFieldGroups inheritedBooleanCondition caseCondition cursor
                possibleTypes runtimeType variableValues)
              outcome := by
  constructor
  · exact fun h => cursorOutcome_to_runtime h hnonempty
  · rintro ⟨runtimeType, hruntime, hgroups⟩
    exact cursorOutcome_of_runtime schema assignment inheritedBooleanCondition
      caseCondition cursor possibleTypes runtimeType variableValues outcome hruntime hgroups

private theorem cursorOutcome_to_typeFree
    {semantics : OutcomeSemantics.{u}} {schema : Schema}
    {assignment : BooleanAssignment}
    {inheritedBooleanCondition caseCondition : List BooleanLiteral}
    {cursor : CaseCursor} {possibleTypes : PossibleTypeRegion}
    {runtimeType : Name} {variableValues : VariableValues}
    {outcome : semantics.Summary}
    (houtcome
      : CaseCursor.ContextOutcome semantics schema assignment
          (.concrete variableValues) inheritedBooleanCondition caseCondition cursor
          possibleTypes outcome)
    (htypes
      : (CaseTrace.withCaseCondition caseCondition
          (CaseTrace.ofCursor variableValues runtimeType cursor)).typeConditions
        = [])
    : CaseCursor.ContextFieldGroupsOutcome semantics schema assignment
        (.concrete variableValues)
        (cursorFieldGroups inheritedBooleanCondition caseCondition cursor possibleTypes
          runtimeType variableValues)
        outcome := by
  cases houtcome with
  | noTypeRegion assignment inherited caseCondition cursor possibleTypes
      branch rest typeName hbranches hcondition hregions =>
      simp [CaseTrace.withCaseCondition, CaseTrace.ofCursor,
        CaseTrace.ofBranches, CaseTrace.branchObservation,
        CaseTrace.Trace.append, hbranches, hcondition] at htypes
  | selectTypeRegion assignment inherited caseCondition cursor possibleTypes
      branch rest typeName region outcome hbranches hcondition hregion hselected hnext =>
      simp [CaseTrace.withCaseCondition, CaseTrace.ofCursor,
        CaseTrace.ofBranches, CaseTrace.branchObservation,
        CaseTrace.Trace.append, hbranches, hcondition] at htypes
  | skipTypeRegion assignment inherited caseCondition cursor possibleTypes
      branch rest typeName region outcome hbranches hcondition hregion hskipped hnext =>
      simp [CaseTrace.withCaseCondition, CaseTrace.ofCursor,
        CaseTrace.ofBranches, CaseTrace.branchObservation,
        CaseTrace.Trace.append, hbranches, hcondition] at htypes
  | knownBoolean assignment inherited caseCondition cursor possibleTypes
      branch rest literal value outcome hbranches hcondition hstatus hnext =>
      have hvalue
          : value = CaseForest.booleanValue variableValues literal.variableName := by
        rw [CaseCursor.BooleanEnvironment.concrete_statusForVariable] at hstatus
        cases hlookup
              : inputValueBoolean? variableValues (.variable literal.variableName) with
        | none => simpa [hlookup, CaseForest.booleanValue] using hstatus
        | some selected => simpa [hlookup, CaseForest.booleanValue] using hstatus.symm
      have htrace := cursorTrace_resolveBoolean variableValues runtimeType caseCondition
        cursor branch rest literal hbranches hcondition
      have hnextTypes :
          (CaseTrace.withCaseCondition
            ((if value then .positive literal.variableName else
              .negative literal.variableName) :: caseCondition)
            (CaseTrace.ofCursor variableValues runtimeType
              (cursor.resolveBooleanBranch branch.body rest literal value))).typeConditions =
            [] := by
        subst value
        rw [← htrace]
        exact htypes
      have hgroups := cursorOutcome_to_typeFree hnext hnextTypes
      have hfieldGroups :
          cursorFieldGroups inheritedBooleanCondition caseCondition cursor possibleTypes
              runtimeType variableValues =
            cursorFieldGroups inheritedBooleanCondition
              ((if value then .positive literal.variableName else
                .negative literal.variableName) :: caseCondition)
              (cursor.resolveBooleanBranch branch.body rest literal value) possibleTypes
              runtimeType variableValues := by
        unfold cursorFieldGroups
        rw [RuntimeCase.resolve_booleanLiteral inheritedBooleanCondition caseCondition
          cursor possibleTypes runtimeType variableValues branch rest literal hbranches
          hcondition]
        unfold CaseForest.booleanValue at hvalue
        rw [← hvalue]
      rwa [hfieldGroups]
  | splitBoolean assignment inherited caseCondition cursor possibleTypes
      branch rest literal outcome hbranches hcondition hstatus hnext =>
      rw [CaseCursor.BooleanEnvironment.concrete_statusForVariable] at hstatus
      cases hlookup : inputValueBoolean? variableValues (.variable literal.variableName) <;>
        simp [hlookup] at hstatus
  | fields assignment inherited caseCondition cursor possibleTypes outcome
      hbranches hgroups =>
      have hfieldGroups :
          cursorFieldGroups inheritedBooleanCondition caseCondition cursor possibleTypes
              runtimeType variableValues =
            cursor.fieldGroups
              (Internal.extendBooleanCondition inheritedBooleanCondition caseCondition)
              possibleTypes := by
        unfold cursorFieldGroups
        rw [RuntimeCase.resolve_nil inheritedBooleanCondition caseCondition cursor
          possibleTypes runtimeType variableValues hbranches]
      rwa [hfieldGroups]
termination_by caseCursorUnresolvedCount cursor
decreasing_by
  all_goals apply cursorBoolean_unresolved_lt <;> assumption

private theorem cursorOutcome_of_typeFree
    {semantics : OutcomeSemantics.{u}} (schema : Schema)
    (assignment : BooleanAssignment)
    (inheritedBooleanCondition caseCondition : List BooleanLiteral)
    (cursor : CaseCursor) (possibleTypes : PossibleTypeRegion)
    (runtimeType : Name) (variableValues : VariableValues)
    (outcome : semantics.Summary)
    (htypes
      : (CaseTrace.withCaseCondition caseCondition
          (CaseTrace.ofCursor variableValues runtimeType cursor)).typeConditions
        = [])
    (hgroups
      : CaseCursor.ContextFieldGroupsOutcome semantics schema assignment
          (.concrete variableValues)
          (cursorFieldGroups inheritedBooleanCondition caseCondition cursor possibleTypes
            runtimeType variableValues)
          outcome)
    : CaseCursor.ContextOutcome semantics schema assignment (.concrete variableValues)
        inheritedBooleanCondition caseCondition cursor possibleTypes outcome := by
  cases hbranches : cursor.pendingBranches with
  | nil =>
      apply CaseCursor.ContextOutcome.fields assignment (.concrete variableValues)
        inheritedBooleanCondition caseCondition cursor possibleTypes outcome hbranches
      have hfieldGroups :
          cursorFieldGroups inheritedBooleanCondition caseCondition cursor possibleTypes
              runtimeType variableValues =
            cursor.fieldGroups
              (Internal.extendBooleanCondition inheritedBooleanCondition caseCondition)
              possibleTypes := by
        unfold cursorFieldGroups
        rw [RuntimeCase.resolve_nil inheritedBooleanCondition caseCondition cursor
          possibleTypes runtimeType variableValues hbranches]
      rwa [← hfieldGroups]
  | cons branch rest =>
      cases hcondition : branch.condition with
      | typeCondition typeName =>
          simp [CaseTrace.withCaseCondition, CaseTrace.ofCursor,
            CaseTrace.ofBranches, CaseTrace.branchObservation,
            CaseTrace.Trace.append, hbranches, hcondition] at htypes
      | booleanLiteral literal =>
          let value := CaseForest.booleanValue variableValues literal.variableName
          have hstatus :
              (CaseCursor.BooleanEnvironment.concrete variableValues).statusForVariable
                literal.variableName = some value := by
            rw [CaseCursor.BooleanEnvironment.concrete_statusForVariable]
            cases hlookup : inputValueBoolean? variableValues
                (.variable literal.variableName) <;>
              simp [value, CaseForest.booleanValue, hlookup]
          have htrace := cursorTrace_resolveBoolean variableValues runtimeType
            caseCondition cursor branch rest literal hbranches hcondition
          have hnextTypes :
              (CaseTrace.withCaseCondition
                ((if value then .positive literal.variableName else
                  .negative literal.variableName) :: caseCondition)
                (CaseTrace.ofCursor variableValues runtimeType
                  (cursor.resolveBooleanBranch branch.body rest literal value))).typeConditions =
                [] := by
            rw [← htrace]
            exact htypes
          apply CaseCursor.ContextOutcome.knownBoolean assignment
            (.concrete variableValues) inheritedBooleanCondition caseCondition cursor
            possibleTypes branch rest literal value outcome hbranches hcondition hstatus
          apply cursorOutcome_of_typeFree schema assignment inheritedBooleanCondition
            ((if value then .positive literal.variableName else
              .negative literal.variableName) :: caseCondition)
            (cursor.resolveBooleanBranch branch.body rest literal value) possibleTypes
            runtimeType variableValues outcome hnextTypes
          have hfieldGroups :
              cursorFieldGroups inheritedBooleanCondition caseCondition cursor
                  possibleTypes runtimeType variableValues =
                cursorFieldGroups inheritedBooleanCondition
                  ((if value then .positive literal.variableName else
                    .negative literal.variableName) :: caseCondition)
                  (cursor.resolveBooleanBranch branch.body rest literal value)
                  possibleTypes runtimeType variableValues := by
            unfold cursorFieldGroups
            rw [RuntimeCase.resolve_booleanLiteral inheritedBooleanCondition caseCondition
              cursor possibleTypes runtimeType variableValues branch rest literal hbranches
              hcondition]
            rfl
          rwa [← hfieldGroups]
termination_by caseCursorUnresolvedCount cursor
decreasing_by
  all_goals apply cursorBoolean_unresolved_lt <;> assumption

private theorem cursorOutcome_iff_typeFree
    {semantics : OutcomeSemantics.{u}} (schema : Schema)
    (assignment : BooleanAssignment)
    (inheritedBooleanCondition caseCondition : List BooleanLiteral)
    (cursor : CaseCursor) (possibleTypes : PossibleTypeRegion)
    (runtimeType : Name) (variableValues : VariableValues)
    (outcome : semantics.Summary)
    (htypes
      : (CaseTrace.withCaseCondition caseCondition
          (CaseTrace.ofCursor variableValues runtimeType cursor)).typeConditions
        = [])
    : CaseCursor.ContextOutcome semantics schema assignment (.concrete variableValues)
        inheritedBooleanCondition caseCondition cursor possibleTypes outcome
      ↔ CaseCursor.ContextFieldGroupsOutcome semantics schema assignment
          (.concrete variableValues)
          (cursorFieldGroups inheritedBooleanCondition caseCondition cursor possibleTypes
            runtimeType variableValues)
          outcome := by
  constructor
  · exact fun h => cursorOutcome_to_typeFree h htypes
  · exact fun h => cursorOutcome_of_typeFree schema assignment
      inheritedBooleanCondition caseCondition cursor possibleTypes runtimeType
      variableValues outcome htypes h

private theorem childOutcome_iff_of_context
    {semantics : OutcomeSemantics.{u}} (schema : Schema)
    (assignment : BooleanAssignment) (variableValues : VariableValues)
    (group : CollectedFieldGroup) (parentTypes : TypeNames)
    (outcome : semantics.Summary)
    (hcontext
      : ∀ childParentType,
          childParentType ∈ parentTypes
          → ∀ childOutcome,
              let childTree :=
                group.childTreeWithKnownFalsePruning schema childParentType variableValues
              CaseForestProof.ContextOutcome semantics schema
                group.childInheritedBooleanCondition (.ofConditionTree childTree)
                childTree.condition.possibleTypes variableValues variableValues
                childOutcome
              ↔ CaseCursor.ContextOutcome semantics schema assignment
                  (.concrete variableValues) group.childInheritedBooleanCondition []
                  (.ofConditionTree childTree) childTree.condition.possibleTypes
                  childOutcome)
    : CaseForestProof.ContextChildTypesOutcome semantics schema group parentTypes
        variableValues variableValues outcome
      ↔ CaseCursor.ContextChildTypesOutcome semantics schema assignment
          (.concrete variableValues) group parentTypes outcome := by
  constructor
  · intro hchild
    cases hchild with
    | none => exact .none assignment (.concrete variableValues) group
    | some _ _ _ _ childParentType _ hparentType hchild =>
        exact .some assignment (.concrete variableValues) group parentTypes
          childParentType outcome hparentType
          ((hcontext childParentType hparentType outcome).mp hchild)
  · intro hchild
    cases hchild with
    | none => exact .none group variableValues variableValues
    | some _ _ _ childParentType _ hparentType hchild =>
        exact .some group parentTypes variableValues variableValues childParentType
          outcome hparentType
          ((hcontext childParentType hparentType outcome).mpr hchild)

private theorem fieldGroupsOutcome_iff_of_context
    {semantics : OutcomeSemantics.{u}} (schema : Schema)
    (assignment : BooleanAssignment) (variableValues : VariableValues)
    (groups : List CollectedFieldGroup) (outcome : semantics.Summary)
    (hcontext
      : ∀ group,
          group ∈ groups
          → ∀ childParentType,
              childParentType ∈ childParentTypes schema group
              → ∀ childOutcome,
                  let childTree :=
                    group.childTreeWithKnownFalsePruning schema childParentType
                      variableValues
                  CaseForestProof.ContextOutcome semantics schema
                    group.childInheritedBooleanCondition (.ofConditionTree childTree)
                    childTree.condition.possibleTypes variableValues variableValues
                    childOutcome
                  ↔ CaseCursor.ContextOutcome semantics schema assignment
                      (.concrete variableValues) group.childInheritedBooleanCondition []
                      (.ofConditionTree childTree) childTree.condition.possibleTypes
                      childOutcome)
    : CaseForestProof.ContextFieldGroupsOutcome semantics schema groups variableValues
        variableValues outcome
      ↔ CaseCursor.ContextFieldGroupsOutcome semantics schema assignment
          (.concrete variableValues) groups outcome := by
  induction groups generalizing outcome with
  | nil =>
      constructor <;> intro hgroups <;> cases hgroups
      · exact .nil assignment (.concrete variableValues)
      · exact .nil variableValues variableValues
  | cons group rest ih =>
      constructor
      · intro hgroups
        cases hgroups with
        | cons _ _ _ _ children fieldOutcome restOutcome hchildren hfield hrest =>
            exact .cons assignment (.concrete variableValues) group rest children
              fieldOutcome restOutcome
              ((childOutcome_iff_of_context schema assignment variableValues group
                  (childParentTypes schema group) children
                  (hcontext group (by simp))).mp
                hchildren) hfield
              ((ih restOutcome
                  (fun candidate hcandidate =>
                    hcontext candidate (by simp [hcandidate]))).mp
                hrest)
      · intro hgroups
        cases hgroups with
        | cons _ _ _ children fieldOutcome restOutcome hchildren hfield hrest =>
            exact .cons group rest variableValues variableValues children fieldOutcome
              restOutcome
              ((childOutcome_iff_of_context schema assignment variableValues group
                  (childParentTypes schema group) children
                  (hcontext group (by simp))).mpr
                hchildren) hfield
              ((ih restOutcome
                  (fun candidate hcandidate =>
                    hcontext candidate (by simp [hcandidate]))).mpr
                hrest)

private theorem conditionTreeOutcome_iff
    {semantics : OutcomeSemantics.{u}} (schema : Schema)
    (assignment : BooleanAssignment)
    (inheritedBooleanCondition : List BooleanLiteral) (tree : Tree)
    (variableValues : VariableValues) (outcome : semantics.Summary)
    (hcoherent : tree.BranchesCoherent schema inheritedBooleanCondition)
    (hnormalized
      : Internal.extendBooleanCondition inheritedBooleanCondition []
        = inheritedBooleanCondition)
    (hinherited : booleanConditionAllows variableValues inheritedBooleanCondition = true)
    : CaseForestProof.ContextOutcome semantics schema inheritedBooleanCondition
        (.ofConditionTree tree) tree.condition.possibleTypes variableValues
        variableValues outcome
      ↔ CaseCursor.ContextOutcome semantics schema assignment
          (.concrete variableValues) inheritedBooleanCondition []
          (.ofConditionTree tree) tree.condition.possibleTypes outcome := by
  cases hpossible : tree.condition.possibleTypes with
  | nil =>
      let runtimeType : Name := ""
      let trace := CaseTrace.ofTree variableValues runtimeType tree
      have htraceTypes : trace.typeConditions = [] :=
        treeTrace_typeFree_of_coherent schema inheritedBooleanCondition variableValues
          runtimeType tree hpossible hcoherent
      have hforestTypes :
          (CaseTrace.ofForest variableValues runtimeType
            (.ofConditionTree tree)).typeConditions = [] := by
        simpa [trace, CaseTrace.ofForest, CaseTrace.ofTrees, CaseForest.ofConditionTree]
          using htraceTypes
      have hcursorTypes :
          (CaseTrace.withCaseCondition []
            (CaseTrace.ofCursor variableValues runtimeType
              (.ofConditionTree tree))).typeConditions = [] := by
        simpa [trace, CaseTrace.withCaseCondition, CaseTrace.ofCursor,
          CaseCursor.ofConditionTree, CaseCursor.namedFields, CaseTrace.ofTree]
          using htraceTypes
      have hforestTrace :
          CaseTrace.ofForest variableValues runtimeType (.ofConditionTree tree) =
            trace := by
        exact forestTrace_ofConditionTree variableValues runtimeType tree
      have hcursorTrace :
          CaseTrace.withCaseCondition []
              (CaseTrace.ofCursor variableValues runtimeType (.ofConditionTree tree)) =
            trace := by
        exact cursorTrace_ofConditionTree variableValues runtimeType tree
      rw [forestOutcome_iff_typeFree schema inheritedBooleanCondition
        (.ofConditionTree tree) [] runtimeType variableValues
        variableValues outcome hforestTypes]
      rw [cursorOutcome_iff_typeFree schema assignment inheritedBooleanCondition []
        (.ofConditionTree tree) [] runtimeType variableValues
        outcome hcursorTypes]
      let groups := CaseTrace.fieldGroups inheritedBooleanCondition [] runtimeType trace
      have hforestGroups :
          CaseForestRuntimeCase.fieldGroups "" inheritedBooleanCondition
              (.ofConditionTree tree) [] runtimeType
              variableValues = groups := by
        rw [CaseForestRuntimeCase.fieldGroups_eq_trace_of_typeFree ""
          inheritedBooleanCondition (.ofConditionTree tree)
          [] runtimeType variableValues hnormalized hinherited hforestTypes]
        exact congrArg (CaseTrace.fieldGroups inheritedBooleanCondition [] runtimeType)
          hforestTrace
      have hcursorGroups :
          cursorFieldGroups inheritedBooleanCondition [] (.ofConditionTree tree)
              [] runtimeType variableValues = groups := by
        rw [cursorFieldGroups_eq_trace_of_typeFree inheritedBooleanCondition []
          (.ofConditionTree tree) [] runtimeType
          variableValues hcursorTypes]
        exact congrArg (CaseTrace.fieldGroups inheritedBooleanCondition [] runtimeType)
          hcursorTrace
      rw [hforestGroups, hcursorGroups]
      apply fieldGroupsOutcome_iff_of_context schema assignment variableValues groups
        outcome
      intro group hgroup childParentType hparentType childOutcome
      let childTree := group.childTreeWithKnownFalsePruning schema childParentType
        variableValues
      have hcontext := CaseTrace.mem_fieldGroups_context inheritedBooleanCondition
        [] runtimeType trace group hgroup
      have htraceAllows :
          booleanConditionAllows variableValues trace.booleanLiterals.reverse = true := by
        rw [CaseForestRuntimeCase.booleanConditionAllows_reverse]
        exact CaseTrace.ofTree_booleanLiterals_allow variableValues runtimeType tree
      have hgroupAllows :
          booleanConditionAllows variableValues group.inheritedBooleanCondition = true := by
        rw [hcontext.1]
        exact CaseForestRuntimeCase.internalExtend_allows variableValues
          inheritedBooleanCondition trace.booleanLiterals.reverse hinherited htraceAllows
      have hgroupNormalized :
          Internal.extendBooleanCondition group.inheritedBooleanCondition [] =
            group.inheritedBooleanCondition := by
        rw [hcontext.1]
        unfold CaseTrace.inheritedBooleanCondition
        rw [CaseForestRuntimeCase.internalExtend_append variableValues
          inheritedBooleanCondition trace.booleanLiterals.reverse [] hinherited
          htraceAllows (by rfl)]
        simp
      have hchildInherited :
          group.childInheritedBooleanCondition = group.inheritedBooleanCondition := by
        unfold CollectedFieldGroup.childInheritedBooleanCondition
        change Internal.extendBooleanCondition group.inheritedBooleanCondition
          group.condition.booleanCondition = group.inheritedBooleanCondition
        rw [hcontext.2, hgroupNormalized]
      have hchildCoherent :
          childTree.BranchesCoherent schema group.childInheritedBooleanCondition := by
        exact ofSelectionSetInScopeWithKnownFalsePruning_branchesCoherent schema
          childParentType group.childInheritedBooleanCondition variableValues
          group.mergedSelectionSet
      have hdepth := CaseForestRuntimeCase.fieldGroups_responseDepth_le ""
        inheritedBooleanCondition (.ofConditionTree tree) []
        runtimeType variableValues
      rw [hforestGroups] at hdepth
      have hgroupDepth := Nat.le_trans
        (_root_.GraphQL.TreeSummary.Measure.collectedFieldGroupResponseDepth_le_of_mem
          group groups hgroup) hdepth
      have hchildDepth : conditionTreeResponseDepth childTree <
          conditionTreeResponseDepth tree := by
        have hextract :=
          conditionTreeResponseDepth_ofSelectionSetInScopeWithKnownFalsePruning schema
            childParentType group.childInheritedBooleanCondition variableValues
            group.mergedSelectionSet
        have hgroupDepth' : collectedFieldGroupResponseDepth group ≤
            conditionTreeResponseDepth tree := by
          simpa [CaseForest.ofConditionTree, caseForestResponseDepth,
            activeTreesResponseDepth]
            using hgroupDepth
        exact Nat.lt_of_le_of_lt hextract
          (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hgroupDepth')
      apply conditionTreeOutcome_iff schema assignment
        group.childInheritedBooleanCondition childTree variableValues childOutcome
        hchildCoherent
      · simpa [hchildInherited] using hgroupNormalized
      · simpa [hchildInherited] using hgroupAllows
  | cons runtimeType rest =>
      have hnonempty : tree.condition.possibleTypes ≠ [] := by
        simp [hpossible]
      rw [forestOutcome_iff_runtime schema inheritedBooleanCondition
        (.ofConditionTree tree) (runtimeType :: rest) variableValues
        variableValues outcome (by simp)]
      rw [cursorOutcome_iff_runtime schema assignment inheritedBooleanCondition []
        (.ofConditionTree tree) (runtimeType :: rest) variableValues outcome
        (by simp)]
      constructor
      · rintro ⟨selectedType, hselectedType, hgroups⟩
        refine ⟨selectedType, hselectedType, ?_⟩
        let trace := CaseTrace.ofTree variableValues selectedType tree
        let groups := CaseTrace.fieldGroups inheritedBooleanCondition
          (runtimeType :: rest) selectedType trace
        have hforestGroups :
            CaseForestRuntimeCase.fieldGroups "" inheritedBooleanCondition
                (.ofConditionTree tree) (runtimeType :: rest) selectedType
                variableValues = groups := by
          rw [CaseForestRuntimeCase.fieldGroups_eq_trace ""
            inheritedBooleanCondition (.ofConditionTree tree)
            (runtimeType :: rest) selectedType variableValues hnormalized
            hinherited hselectedType]
          exact congrArg
            (CaseTrace.fieldGroups inheritedBooleanCondition (runtimeType :: rest)
              selectedType)
            (forestTrace_ofConditionTree variableValues selectedType tree)
        have hcursorGroups :
            cursorFieldGroups inheritedBooleanCondition [] (.ofConditionTree tree)
                (runtimeType :: rest) selectedType variableValues = groups := by
          change RuntimeCase.fieldGroupsFrom inheritedBooleanCondition []
            (.ofConditionTree tree) (runtimeType :: rest) selectedType variableValues =
              groups
          rw [RuntimeCase.fieldGroupsFrom_eq_trace inheritedBooleanCondition []
            (.ofConditionTree tree) (runtimeType :: rest) selectedType
            variableValues hselectedType]
          exact congrArg
            (CaseTrace.fieldGroups inheritedBooleanCondition (runtimeType :: rest)
              selectedType)
            (cursorTrace_ofConditionTree variableValues selectedType tree)
        rw [hforestGroups] at hgroups
        rw [hcursorGroups]
        apply (fieldGroupsOutcome_iff_of_context schema assignment variableValues
          groups outcome ?_).mp hgroups
        intro group hgroup childParentType hparentType childOutcome
        let childTree := group.childTreeWithKnownFalsePruning schema childParentType
          variableValues
        have hcontext := CaseTrace.mem_fieldGroups_context inheritedBooleanCondition
          (runtimeType :: rest) selectedType trace group hgroup
        have htraceAllows :
            booleanConditionAllows variableValues trace.booleanLiterals.reverse = true := by
          rw [CaseForestRuntimeCase.booleanConditionAllows_reverse]
          exact CaseTrace.ofTree_booleanLiterals_allow variableValues selectedType tree
        have hgroupAllows :
            booleanConditionAllows variableValues group.inheritedBooleanCondition = true := by
          rw [hcontext.1]
          exact CaseForestRuntimeCase.internalExtend_allows variableValues
            inheritedBooleanCondition trace.booleanLiterals.reverse hinherited htraceAllows
        have hgroupNormalized :
            Internal.extendBooleanCondition group.inheritedBooleanCondition [] =
              group.inheritedBooleanCondition := by
          rw [hcontext.1]
          unfold CaseTrace.inheritedBooleanCondition
          rw [CaseForestRuntimeCase.internalExtend_append variableValues
            inheritedBooleanCondition trace.booleanLiterals.reverse [] hinherited
            htraceAllows (by rfl)]
          simp
        have hchildInherited :
            group.childInheritedBooleanCondition = group.inheritedBooleanCondition := by
          unfold CollectedFieldGroup.childInheritedBooleanCondition
          change Internal.extendBooleanCondition group.inheritedBooleanCondition
            group.condition.booleanCondition = group.inheritedBooleanCondition
          rw [hcontext.2, hgroupNormalized]
        have hchildCoherent :
            childTree.BranchesCoherent schema group.childInheritedBooleanCondition :=
          ofSelectionSetInScopeWithKnownFalsePruning_branchesCoherent schema
            childParentType group.childInheritedBooleanCondition variableValues
            group.mergedSelectionSet
        have hdepth := CaseForestRuntimeCase.fieldGroups_responseDepth_le ""
          inheritedBooleanCondition (.ofConditionTree tree) (runtimeType :: rest)
          selectedType variableValues
        rw [hforestGroups] at hdepth
        have hgroupDepth := Nat.le_trans
          (_root_.GraphQL.TreeSummary.Measure.collectedFieldGroupResponseDepth_le_of_mem
            group groups hgroup) hdepth
        have hchildDepth : conditionTreeResponseDepth childTree <
            conditionTreeResponseDepth tree := by
          have hextract :=
            conditionTreeResponseDepth_ofSelectionSetInScopeWithKnownFalsePruning schema
              childParentType group.childInheritedBooleanCondition variableValues
              group.mergedSelectionSet
          have hgroupDepth' : collectedFieldGroupResponseDepth group ≤
              conditionTreeResponseDepth tree := by
            simpa [CaseForest.ofConditionTree, caseForestResponseDepth,
              activeTreesResponseDepth]
              using hgroupDepth
          exact Nat.lt_of_le_of_lt hextract
            (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hgroupDepth')
        apply conditionTreeOutcome_iff schema assignment
          group.childInheritedBooleanCondition childTree variableValues childOutcome
          hchildCoherent
        · simpa [hchildInherited] using hgroupNormalized
        · simpa [hchildInherited] using hgroupAllows
      · rintro ⟨selectedType, hselectedType, hgroups⟩
        refine ⟨selectedType, hselectedType, ?_⟩
        let trace := CaseTrace.ofTree variableValues selectedType tree
        let groups := CaseTrace.fieldGroups inheritedBooleanCondition
          (runtimeType :: rest) selectedType trace
        have hforestGroups :
            CaseForestRuntimeCase.fieldGroups "" inheritedBooleanCondition
                (.ofConditionTree tree) (runtimeType :: rest) selectedType
                variableValues = groups := by
          rw [CaseForestRuntimeCase.fieldGroups_eq_trace ""
            inheritedBooleanCondition (.ofConditionTree tree)
            (runtimeType :: rest) selectedType variableValues hnormalized
            hinherited hselectedType]
          exact congrArg
            (CaseTrace.fieldGroups inheritedBooleanCondition (runtimeType :: rest)
              selectedType)
            (forestTrace_ofConditionTree variableValues selectedType tree)
        have hcursorGroups :
            cursorFieldGroups inheritedBooleanCondition [] (.ofConditionTree tree)
                (runtimeType :: rest) selectedType variableValues = groups := by
          change RuntimeCase.fieldGroupsFrom inheritedBooleanCondition []
            (.ofConditionTree tree) (runtimeType :: rest) selectedType variableValues =
              groups
          rw [RuntimeCase.fieldGroupsFrom_eq_trace inheritedBooleanCondition []
            (.ofConditionTree tree) (runtimeType :: rest) selectedType
            variableValues hselectedType]
          exact congrArg
            (CaseTrace.fieldGroups inheritedBooleanCondition (runtimeType :: rest)
              selectedType)
            (cursorTrace_ofConditionTree variableValues selectedType tree)
        rw [hcursorGroups] at hgroups
        rw [hforestGroups]
        apply (fieldGroupsOutcome_iff_of_context schema assignment variableValues
          groups outcome ?_).mpr hgroups
        intro group hgroup childParentType hparentType childOutcome
        let childTree := group.childTreeWithKnownFalsePruning schema childParentType
          variableValues
        have hcontext := CaseTrace.mem_fieldGroups_context inheritedBooleanCondition
          (runtimeType :: rest) selectedType trace group hgroup
        have htraceAllows :
            booleanConditionAllows variableValues trace.booleanLiterals.reverse = true := by
          rw [CaseForestRuntimeCase.booleanConditionAllows_reverse]
          exact CaseTrace.ofTree_booleanLiterals_allow variableValues selectedType tree
        have hgroupAllows :
            booleanConditionAllows variableValues group.inheritedBooleanCondition = true := by
          rw [hcontext.1]
          exact CaseForestRuntimeCase.internalExtend_allows variableValues
            inheritedBooleanCondition trace.booleanLiterals.reverse hinherited htraceAllows
        have hgroupNormalized :
            Internal.extendBooleanCondition group.inheritedBooleanCondition [] =
              group.inheritedBooleanCondition := by
          rw [hcontext.1]
          unfold CaseTrace.inheritedBooleanCondition
          rw [CaseForestRuntimeCase.internalExtend_append variableValues
            inheritedBooleanCondition trace.booleanLiterals.reverse [] hinherited
            htraceAllows (by rfl)]
          simp
        have hchildInherited :
            group.childInheritedBooleanCondition = group.inheritedBooleanCondition := by
          unfold CollectedFieldGroup.childInheritedBooleanCondition
          change Internal.extendBooleanCondition group.inheritedBooleanCondition
            group.condition.booleanCondition = group.inheritedBooleanCondition
          rw [hcontext.2, hgroupNormalized]
        have hchildCoherent :
            childTree.BranchesCoherent schema group.childInheritedBooleanCondition :=
          ofSelectionSetInScopeWithKnownFalsePruning_branchesCoherent schema
            childParentType group.childInheritedBooleanCondition variableValues
            group.mergedSelectionSet
        have hdepth := CaseForestRuntimeCase.fieldGroups_responseDepth_le ""
          inheritedBooleanCondition (.ofConditionTree tree) (runtimeType :: rest)
          selectedType variableValues
        rw [hforestGroups] at hdepth
        have hgroupDepth := Nat.le_trans
          (_root_.GraphQL.TreeSummary.Measure.collectedFieldGroupResponseDepth_le_of_mem
            group groups hgroup) hdepth
        have hchildDepth : conditionTreeResponseDepth childTree <
            conditionTreeResponseDepth tree := by
          have hextract :=
            conditionTreeResponseDepth_ofSelectionSetInScopeWithKnownFalsePruning schema
              childParentType group.childInheritedBooleanCondition variableValues
              group.mergedSelectionSet
          have hgroupDepth' : collectedFieldGroupResponseDepth group ≤
              conditionTreeResponseDepth tree := by
            simpa [CaseForest.ofConditionTree, caseForestResponseDepth,
              activeTreesResponseDepth]
              using hgroupDepth
          exact Nat.lt_of_le_of_lt hextract
            (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hgroupDepth')
        apply conditionTreeOutcome_iff schema assignment
          group.childInheritedBooleanCondition childTree variableValues childOutcome
          hchildCoherent
        · simpa [hchildInherited] using hgroupNormalized
        · simpa [hchildInherited] using hgroupAllows
termination_by conditionTreeResponseDepth tree
decreasing_by
  all_goals exact hchildDepth

theorem conditionTreeOutcomes_concrete_iff
    {semantics : OutcomeSemantics.{u}} (schema : Schema)
    (inheritedBooleanCondition : List BooleanLiteral) (tree : Tree)
    (variableValues : VariableValues) (outcome : semantics.Summary)
    (hcoherent : tree.BranchesCoherent schema inheritedBooleanCondition)
    (hnormalized
      : Internal.extendBooleanCondition inheritedBooleanCondition []
        = inheritedBooleanCondition)
    (hinherited : booleanConditionAllows variableValues inheritedBooleanCondition = true)
    : CaseForestProof.conditionTreeOutcomes semantics schema
        inheritedBooleanCondition tree variableValues variableValues outcome
      ↔ CaseCursor.conditionTreeOutcomes semantics schema
          inheritedBooleanCondition tree (.concrete variableValues) outcome := by
  let assignment : BooleanAssignment := fun variableName =>
    CaseForest.booleanValue variableValues variableName
  have hextends : assignment.Extends (.concrete variableValues) := by
    intro variableName value hstatus
    rw [CaseCursor.BooleanEnvironment.concrete_statusForVariable] at hstatus
    cases hlookup : inputValueBoolean? variableValues (.variable variableName) with
    | none => simpa [assignment, CaseForest.booleanValue, hlookup] using hstatus.symm
    | some selected => simpa [assignment, CaseForest.booleanValue, hlookup] using hstatus
  unfold CaseForestProof.conditionTreeOutcomes CaseCursor.conditionTreeOutcomes
  constructor
  · intro houtcome
    exact ⟨assignment, hextends,
      (conditionTreeOutcome_iff schema assignment inheritedBooleanCondition tree
        variableValues outcome hcoherent hnormalized hinherited).mp houtcome⟩
  · rintro ⟨selectedAssignment, _hextends, houtcome⟩
    exact (conditionTreeOutcome_iff schema selectedAssignment
      inheritedBooleanCondition tree variableValues outcome hcoherent hnormalized
      hinherited).mpr houtcome

theorem selectionSetOutcomes_concrete_iff
    {semantics : OutcomeSemantics.{u}} (schema : Schema)
    (parentType : Name) (selectionSet : List Selection)
    (variableValues : VariableValues) (outcome : semantics.Summary)
    : CaseForestProof.selectionSetOutcomes semantics schema parentType [] selectionSet
        variableValues outcome
      ↔ CaseCursor.selectionSetOutcomes semantics schema parentType [] selectionSet
          (.concrete variableValues) outcome := by
  unfold CaseForestProof.selectionSetOutcomes CaseCursor.selectionSetOutcomes
  apply conditionTreeOutcomes_concrete_iff schema []
  · exact ofSelectionSetInScopeWithKnownFalsePruning_branchesCoherent schema
      parentType [] variableValues selectionSet
  · rfl
  · rfl

theorem operationOutcomesWithVariables_iff_forest
    {semantics : OutcomeSemantics.{u}} (schema : Schema)
    (variableValues : VariableValues) (operation : Operation)
    (outcome : semantics.Summary)
    : operationOutcomesWithVariables semantics schema variableValues operation outcome
      ↔ CaseForestProof.selectionSetOutcomes semantics schema
          (operation.rootType schema) [] operation.selectionSet
          (Execution.coerceVariableValues operation variableValues) outcome := by
  unfold operationOutcomesWithVariables
  exact (selectionSetOutcomes_concrete_iff schema (operation.rootType schema)
    operation.selectionSet (Execution.coerceVariableValues operation variableValues)
    outcome).symm

end CaseForestOutcomeLifting
end ExactCases
end TreeSummary
end GraphQL
