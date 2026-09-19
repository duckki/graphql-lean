import GraphQL.Theories.TreeSummary.ExactCases
import Proofs.GraphQL.Theories.SelectionConditions.Canonical
import Proofs.GraphQL.Theories.SelectionConditions.Runtime
import Proofs.GraphQL.Theories.TreeSummary.PossibleTypeRegions

/-! A proof-only, scheduler-independent description of one concrete exact case. -/

namespace GraphQL
namespace TreeSummary
namespace ExactCases

open GraphQL.ConditionTree
open GraphQL.Execution
open GraphQL.SelectionConditions

namespace CaseTrace

structure Trace where
  namedFields : List NamedField
  typeConditions : List PossibleTypes
  booleanLiterals : List BooleanLiteral

def Trace.empty : Trace := ⟨[], [], []⟩

def Trace.append (left right : Trace) : Trace :=
  {
    namedFields := left.namedFields ++ right.namedFields
    typeConditions := left.typeConditions ++ right.typeConditions
    booleanLiterals := left.booleanLiterals ++ right.booleanLiterals
  }

@[simp]
theorem Trace.empty_append (trace : Trace) : Trace.empty.append trace = trace := by
  cases trace
  simp [Trace.empty, Trace.append]

@[simp]
theorem Trace.append_empty (trace : Trace) : trace.append Trace.empty = trace := by
  cases trace
  simp [Trace.empty, Trace.append]

theorem Trace.append_assoc (left middle right : Trace)
    : (left.append middle).append right = left.append (middle.append right) := by
  cases left
  cases middle
  cases right
  simp [Trace.append, List.append_assoc]

def selectedLiteral (variableValues : VariableValues) (variableName : Name)
    : BooleanLiteral :=
  if CaseForest.booleanValue variableValues variableName then
    .positive variableName
  else
    .negative variableName

def branchSelected (variableValues : VariableValues) (runtimeType : Name)
    (branch : Branch Tree)
    : Bool :=
  match branch.condition with
  | .typeCondition _typeName => branch.body.condition.possibleTypes.contains runtimeType
  | .booleanLiteral literal =>
      literal.requiredValue == CaseForest.booleanValue variableValues literal.variableName

def branchObservation (variableValues : VariableValues) (branch : Branch Tree) : Trace :=
  match branch.condition with
  | .typeCondition _typeName => ⟨[], [branch.body.condition.possibleTypes], []⟩
  | .booleanLiteral literal =>
      ⟨[], [], [selectedLiteral variableValues literal.variableName]⟩

mutual
  def ofTree (variableValues : VariableValues) (runtimeType : Name) (tree : Tree)
      : Trace :=
    ({
        namedFields := CaseCursor.localNamedFields tree
        typeConditions := []
        booleanLiterals := []
      }
      : Trace).append
      (ofBranches variableValues runtimeType tree.branches)
  termination_by sizeOf tree
  decreasing_by
    cases tree
    simp_wf
    omega

  def ofBranches (variableValues : VariableValues) (runtimeType : Name)
      : List (Branch Tree) -> Trace
    | [] => .empty
    | branch :: rest =>
        let body :=
          if branchSelected variableValues runtimeType branch then
            ofTree variableValues runtimeType branch.body
          else
            .empty
        (branchObservation variableValues branch).append body
        |>.append (ofBranches variableValues runtimeType rest)
  termination_by branches => sizeOf branches
  decreasing_by
    all_goals
      cases branch
      simp_wf
      omega
end

theorem ofBranches_append (variableValues : VariableValues) (runtimeType : Name)
    (left right : List (Branch Tree))
    : ofBranches variableValues runtimeType (left ++ right)
      = (ofBranches variableValues runtimeType left).append
          (ofBranches variableValues runtimeType right) := by
  induction left with
  | nil => simp [ofBranches]
  | cons branch rest ih =>
      simp only [List.cons_append, ofBranches]
      rw [ih]
      simp [Trace.append_assoc]

def ofTrees (variableValues : VariableValues) (runtimeType : Name) (trees : List Tree)
    : Trace :=
  trees.foldr (fun tree rest => (ofTree variableValues runtimeType tree).append rest)
    .empty

@[simp]
theorem ofTrees_nil (variableValues : VariableValues) (runtimeType : Name)
    : ofTrees variableValues runtimeType [] = Trace.empty :=
  rfl

@[simp]
theorem ofTrees_cons (variableValues : VariableValues) (runtimeType : Name)
    (tree : Tree) (rest : List Tree)
    : ofTrees variableValues runtimeType (tree :: rest)
      = (ofTree variableValues runtimeType tree).append
          (ofTrees variableValues runtimeType rest) :=
  rfl

theorem ofTrees_append (variableValues : VariableValues) (runtimeType : Name)
    (left right : List Tree)
    : ofTrees variableValues runtimeType (left ++ right)
      = (ofTrees variableValues runtimeType left).append
          (ofTrees variableValues runtimeType right) := by
  unfold ofTrees
  rw [List.foldr_append]
  have aux : ∀ (items : List Tree) (base : Trace),
      items.foldr (fun tree rest => (ofTree variableValues runtimeType tree).append rest)
          base
        = (items.foldr
            (fun tree rest => (ofTree variableValues runtimeType tree).append rest)
            Trace.empty).append base := by
    intro items base
    induction items generalizing base with
    | nil => simp
    | cons tree rest ih =>
        simp only [List.foldr]
        rw [ih]
        exact (Trace.append_assoc _ _ _).symm
  exact aux left _

def ofCursor (variableValues : VariableValues) (runtimeType : Name) (cursor : CaseCursor)
    : Trace :=
  ({
      namedFields := cursor.namedFields
      typeConditions := []
      booleanLiterals := []
    }
    : Trace).append
    (ofBranches variableValues runtimeType cursor.pendingBranches)

def ofForest (variableValues : VariableValues) (runtimeType : Name) (forest : CaseForest)
    : Trace :=
  ofTrees variableValues runtimeType forest.activeTrees

def withCaseCondition (caseCondition : List BooleanLiteral) (trace : Trace) : Trace :=
  { trace with booleanLiterals := caseCondition.reverse ++ trace.booleanLiterals }

def possibleTypes (scope : PossibleTypes) (runtimeType : Name) (trace : Trace)
    : PossibleTypeRegion :=
  possibleTypeMembershipClass scope trace.typeConditions runtimeType

def inheritedBooleanCondition (inherited : List BooleanLiteral) (trace : Trace)
    : List BooleanLiteral :=
  Internal.extendBooleanCondition inherited trace.booleanLiterals.reverse

def fieldGroups (inherited : List BooleanLiteral) (scope : PossibleTypes)
    (runtimeType : Name) (trace : Trace)
    : List CollectedFieldGroup :=
  TreeSummary.fieldGroupsWithContext (inheritedBooleanCondition inherited trace)
    { possibleTypes := possibleTypes scope runtimeType trace, booleanCondition := [] }
    (ConditionTree.collectFieldGroups trace.namedFields)

theorem mem_fieldGroups_context
    (inherited : List BooleanLiteral) (scope : PossibleTypes)
    (runtimeType : Name) (trace : Trace) (group : CollectedFieldGroup)
    (hgroup : group ∈ fieldGroups inherited scope runtimeType trace)
    : group.inheritedBooleanCondition = inheritedBooleanCondition inherited trace
      ∧ group.condition.booleanCondition = [] := by
  unfold fieldGroups TreeSummary.fieldGroupsWithContext at hgroup
  simp only [List.mem_map] at hgroup
  rcases hgroup with ⟨fieldGroup, _hfieldGroup, rfl⟩
  exact ⟨rfl, rfl⟩

private theorem selectedLiteral_allows
    (variableValues : VariableValues) (variableName : Name)
    : booleanConditionAllows variableValues [selectedLiteral variableValues variableName]
      = true := by
  cases hvalue : inputValueBoolean? variableValues (.variable variableName) with
  | none =>
      simp [selectedLiteral, CaseForest.booleanValue, hvalue,
        booleanConditionAllows, BooleanLiteral.allows, BooleanLiteral.toDirective,
        directiveAllowsSelectionBool]
  | some value =>
      cases value <;>
        simp [selectedLiteral, CaseForest.booleanValue, hvalue,
          booleanConditionAllows, BooleanLiteral.allows, BooleanLiteral.toDirective,
          directiveAllowsSelectionBool]

mutual
  theorem ofTree_booleanLiterals_allow
      (variableValues : VariableValues) (runtimeType : Name) (tree : Tree)
      : booleanConditionAllows variableValues
          (ofTree variableValues runtimeType tree).booleanLiterals
        = true := by
    rw [ofTree]
    simp only [Trace.append, List.nil_append]
    exact ofBranches_booleanLiterals_allow variableValues runtimeType tree.branches
  termination_by sizeOf tree
  decreasing_by
    cases tree
    simp_wf
    omega

  theorem ofBranches_booleanLiterals_allow
      (variableValues : VariableValues) (runtimeType : Name)
      : ∀ branches : List (Branch Tree),
          booleanConditionAllows variableValues
            (ofBranches variableValues runtimeType branches).booleanLiterals
          = true
    | [] => by simp [ofBranches, Trace.empty, booleanConditionAllows]
    | branch :: rest => by
        have hrest := ofBranches_booleanLiterals_allow variableValues runtimeType rest
        cases hcondition : branch.condition with
        | typeCondition typeName =>
            cases hselected : branchSelected variableValues runtimeType branch with
            | false =>
                simp [ofBranches, branchObservation, hcondition, hselected,
                  Trace.empty, Trace.append, hrest]
            | true =>
                simp only [ofBranches, branchObservation, hcondition, hselected,
                  ite_true, Trace.append, List.nil_append]
                rw [booleanConditionAllows_append,
                  ofTree_booleanLiterals_allow variableValues runtimeType branch.body,
                  hrest]
                rfl
        | booleanLiteral literal =>
            have hliteral :
                (selectedLiteral variableValues literal.variableName).allows
                    variableValues = true := by
              simpa [booleanConditionAllows] using
                selectedLiteral_allows variableValues literal.variableName
            cases hselected : branchSelected variableValues runtimeType branch with
            | false =>
                simp [ofBranches, branchObservation, hcondition, hselected,
                  Trace.empty, Trace.append, booleanConditionAllows, hliteral, hrest]
            | true =>
                simp only [ofBranches, branchObservation, hcondition, hselected,
                  ite_true, Trace.append, List.nil_append]
                change booleanConditionAllows variableValues
                    ([selectedLiteral variableValues literal.variableName] ++
                      (ofTree variableValues runtimeType branch.body).booleanLiterals ++
                      (ofBranches variableValues runtimeType rest).booleanLiterals) = true
                rw [booleanConditionAllows_append, booleanConditionAllows_append,
                  selectedLiteral_allows,
                  ofTree_booleanLiterals_allow variableValues runtimeType branch.body,
                  hrest]
                rfl
  termination_by branches => sizeOf branches
  decreasing_by
    all_goals
      cases branch
      simp_wf
      omega
end

theorem ofForest_booleanLiterals_allow
    (variableValues : VariableValues) (runtimeType : Name) (forest : CaseForest)
    : booleanConditionAllows variableValues
        (ofForest variableValues runtimeType forest).booleanLiterals
      = true := by
  unfold ofForest
  induction forest.activeTrees with
  | nil => simp [ofTrees, Trace.empty, booleanConditionAllows]
  | cons tree rest ih =>
      rw [ofTrees_cons]
      simp only [Trace.append]
      rw [booleanConditionAllows_append,
        ofTree_booleanLiterals_allow variableValues runtimeType tree, ih]
      rfl

end CaseTrace
end ExactCases
end TreeSummary
end GraphQL
