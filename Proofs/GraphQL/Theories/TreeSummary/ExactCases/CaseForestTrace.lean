import Proofs.GraphQL.Theories.TreeSummary.ExactCases.CaseTrace

/-! Schedule-independence facts for one batched exact-case frontier. -/

namespace GraphQL
namespace TreeSummary
namespace ExactCases
namespace CaseTrace

open GraphQL.ConditionTree
open GraphQL.Execution

def frontierTypeConditions : List (Branch Tree) -> List PossibleTypes
  | [] => []
  | branch :: rest =>
      match branch.condition with
      | .typeCondition _ =>
          branch.body.condition.possibleTypes :: frontierTypeConditions rest
      | .booleanLiteral _ => frontierTypeConditions rest

def frontierBooleanLiterals (variableValues : VariableValues)
    : List (Branch Tree) -> List BooleanLiteral
  | [] => []
  | branch :: rest =>
      match branch.condition with
      | .typeCondition _ => frontierBooleanLiterals variableValues rest
      | .booleanLiteral literal =>
          selectedLiteral variableValues literal.variableName
          :: frontierBooleanLiterals variableValues rest

private def frontierBooleanVariables : List (Branch Tree) -> BooleanVariableNames
  | [] => []
  | branch :: rest =>
      match branch.condition with
      | .typeCondition _ => frontierBooleanVariables rest
      | .booleanLiteral literal => literal.variableName :: frontierBooleanVariables rest

private theorem frontierTypeConditions_append (left right : List (Branch Tree))
    : frontierTypeConditions (left ++ right)
      = frontierTypeConditions left ++ frontierTypeConditions right := by
  induction left with
  | nil => rfl
  | cons branch rest ih =>
      cases hcondition : branch.condition <;>
        simp [frontierTypeConditions, hcondition, ih]

private theorem frontierBooleanLiterals_append (variableValues : VariableValues)
    (left right : List (Branch Tree))
    : frontierBooleanLiterals variableValues (left ++ right)
      = frontierBooleanLiterals variableValues left
        ++ frontierBooleanLiterals variableValues right := by
  induction left with
  | nil => rfl
  | cons branch rest ih =>
      cases hcondition : branch.condition <;>
        simp [frontierBooleanLiterals, hcondition, ih]

private theorem perm_move_left (left middle right : List α)
    : (left ++ (middle ++ right)).Perm (middle ++ (left ++ right)) := by
  simpa [List.append_assoc]
    using List.Perm.append_right right (List.perm_append_comm (l₁ := left) (l₂ := middle))

private theorem booleanConditionAllows_singleton
    (variableValues : VariableValues) (literal : BooleanLiteral)
    : booleanConditionAllows variableValues [literal]
      = (literal.requiredValue
          == CaseForest.booleanValue variableValues literal.variableName) := by
  cases literal with
  | positive variableName =>
      simp only [booleanConditionAllows, BooleanLiteral.allows,
        BooleanLiteral.toDirective, directiveAllowsSelectionBool,
        BooleanLiteral.requiredValue, BooleanLiteral.variableName, Bool.and_true,
        CaseForest.booleanValue]
      cases hvalue : inputValueBoolean? variableValues (.variable variableName) with
      | none => simp
      | some value => cases value <;> simp
  | negative variableName =>
      simp only [booleanConditionAllows, BooleanLiteral.allows,
        BooleanLiteral.toDirective, directiveAllowsSelectionBool,
        BooleanLiteral.requiredValue, BooleanLiteral.variableName, Bool.and_true,
        CaseForest.booleanValue]
      cases hvalue : inputValueBoolean? variableValues (.variable variableName) with
      | none => simp
      | some value => cases value <;> simp

private theorem possibleTypesSubset_eq_contains_of_constant
    (region allowed : PossibleTypes) (runtimeType : Name)
    (hruntime : runtimeType ∈ region)
    (hconstant
      : ∀ candidate,
          candidate ∈ region -> allowed.contains candidate = allowed.contains runtimeType)
    : possibleTypesSubset region allowed = allowed.contains runtimeType := by
  unfold possibleTypesSubset
  cases hallowed : allowed.contains runtimeType with
  | true =>
      exact List.all_eq_true.mpr fun candidate hcandidate => by
        rw [hconstant candidate hcandidate, hallowed]
  | false =>
      have hnotmem : runtimeType ∉ allowed := by
        intro hmem
        exact Bool.noConfusion
          (hallowed.symm.trans (List.contains_iff_mem.mpr hmem))
      exact List.all_eq_false.mpr ⟨runtimeType, hruntime, by simpa using hnotmem⟩

private theorem typeRegions_uniform
    (forest : CaseForest) (scope : PossibleTypes)
    (region : PossibleTypeRegion) (hregion : region ∈ forest.typeRegions scope)
    (left : Name) (hleft : left ∈ region) (right : Name) (hright : right ∈ region)
    (allowed : PossibleTypes) (hallowed : allowed ∈ forest.typeBranchPossibleTypes)
    : allowed.contains left = allowed.contains right := by
  exact (possibleTypeRegions_exact scope forest.typeBranchPossibleTypes).2.2
    region hregion left hleft right hright allowed hallowed

private theorem branchSelection_eq
    (variableValues : VariableValues) (runtimeType : Name)
    (possibleTypes : PossibleTypeRegion) (branch : Branch Tree)
    (htype
      : match branch.condition with
        | .typeCondition _ =>
            possibleTypesSubset possibleTypes branch.body.condition.possibleTypes
            = branch.body.condition.possibleTypes.contains runtimeType
        | .booleanLiteral _ => True)
    : (match branch.condition with
        | .typeCondition _ =>
            possibleTypesSubset possibleTypes branch.body.condition.possibleTypes
        | .booleanLiteral literal => booleanConditionAllows variableValues [literal])
      = branchSelected variableValues runtimeType branch := by
  cases hcondition : branch.condition with
  | typeCondition typeName => simpa [branchSelected, hcondition] using htype
  | booleanLiteral literal =>
      simp [branchSelected, hcondition, booleanConditionAllows_singleton]

private theorem ofBranches_namedFields
    (variableValues : VariableValues) (runtimeType : Name)
    (possibleTypes : PossibleTypeRegion) (branches : List (Branch Tree))
    (htype
      : ∀ branch,
          branch ∈ branches
          -> match branch.condition with
              | .typeCondition _ =>
                  possibleTypesSubset possibleTypes branch.body.condition.possibleTypes
                  = branch.body.condition.possibleTypes.contains runtimeType
              | .booleanLiteral _ => True)
    : (ofBranches variableValues runtimeType branches).namedFields
      = (ofTrees variableValues runtimeType
          (CaseForest.selectedChildren possibleTypes variableValues
            branches)).namedFields := by
  induction branches with
  | nil => simp [ofBranches, ofTrees, CaseForest.selectedChildren, Trace.empty]
  | cons branch rest ih =>
      have hhead := branchSelection_eq variableValues runtimeType possibleTypes branch
        (htype branch (by simp))
      have hrest : ∀ candidate, candidate ∈ rest ->
          match candidate.condition with
          | .typeCondition _ =>
              possibleTypesSubset possibleTypes candidate.body.condition.possibleTypes
                = candidate.body.condition.possibleTypes.contains runtimeType
          | .booleanLiteral _ => True := by
        intro candidate hcandidate
        exact htype candidate (by simp [hcandidate])
      cases hcondition : branch.condition with
      | typeCondition typeName =>
          simp only [hcondition] at hhead
          cases hvalue
                : possibleTypesSubset possibleTypes
                    branch.body.condition.possibleTypes with
          | false =>
              have hselected : branchSelected variableValues runtimeType branch = false :=
                hhead.symm.trans hvalue
              simp [ofBranches, ofTrees, CaseForest.selectedChildren, hcondition,
                hvalue, hselected, ih hrest, branchObservation, Trace.empty,
                Trace.append]
          | true =>
              have hselected : branchSelected variableValues runtimeType branch = true :=
                hhead.symm.trans hvalue
              simp [ofBranches, ofTrees, CaseForest.selectedChildren, hcondition,
                hvalue, hselected, ih hrest, branchObservation, Trace.empty,
                Trace.append]
      | booleanLiteral literal =>
          simp only [hcondition] at hhead
          cases hvalue : booleanConditionAllows variableValues [literal] with
          | false =>
              have hselected : branchSelected variableValues runtimeType branch = false :=
                hhead.symm.trans hvalue
              simp [ofBranches, ofTrees, CaseForest.selectedChildren, hcondition,
                hvalue, hselected, ih hrest, branchObservation, Trace.empty,
                Trace.append]
          | true =>
              have hselected : branchSelected variableValues runtimeType branch = true :=
                hhead.symm.trans hvalue
              simp [ofBranches, ofTrees, CaseForest.selectedChildren, hcondition,
                hvalue, hselected, ih hrest, branchObservation, Trace.empty,
                Trace.append]

private theorem ofBranches_typeConditions
    (variableValues : VariableValues) (runtimeType : Name)
    (possibleTypes : PossibleTypeRegion) (branches : List (Branch Tree))
    (htype
      : ∀ branch,
          branch ∈ branches
          -> match branch.condition with
              | .typeCondition _ =>
                  possibleTypesSubset possibleTypes branch.body.condition.possibleTypes
                  = branch.body.condition.possibleTypes.contains runtimeType
              | .booleanLiteral _ => True)
    : (ofBranches variableValues runtimeType branches).typeConditions.Perm
        (frontierTypeConditions branches
          ++ (ofTrees variableValues runtimeType
                (CaseForest.selectedChildren possibleTypes variableValues
                  branches)).typeConditions) := by
  induction branches with
  | nil => simp [ofBranches, ofTrees, CaseForest.selectedChildren,
      frontierTypeConditions, Trace.empty]
  | cons branch rest ih =>
      have hhead := branchSelection_eq variableValues runtimeType possibleTypes branch
        (htype branch (by simp))
      have hrest : ∀ candidate, candidate ∈ rest ->
          match candidate.condition with
          | .typeCondition _ =>
              possibleTypesSubset possibleTypes candidate.body.condition.possibleTypes
                = candidate.body.condition.possibleTypes.contains runtimeType
          | .booleanLiteral _ => True := by
        intro candidate hcandidate
        exact htype candidate (by simp [hcandidate])
      have hih := ih hrest
      cases hcondition : branch.condition with
      | typeCondition typeName =>
          simp only [hcondition] at hhead
          cases hvalue
                : possibleTypesSubset possibleTypes
                    branch.body.condition.possibleTypes with
          | false =>
              have hselected : branchSelected variableValues runtimeType branch = false :=
                hhead.symm.trans hvalue
              simpa [ofBranches, ofTrees, CaseForest.selectedChildren,
                frontierTypeConditions, branchObservation, hcondition, hvalue, hselected,
                Trace.append, Trace.empty, List.append_assoc]
                using List.Perm.cons branch.body.condition.possibleTypes hih
          | true =>
              have hselected : branchSelected variableValues runtimeType branch = true :=
                hhead.symm.trans hvalue
              have hfirst := List.Perm.cons branch.body.condition.possibleTypes
                (List.Perm.append_left
                  (ofTree variableValues runtimeType branch.body).typeConditions hih)
              have hsecond := List.Perm.cons branch.body.condition.possibleTypes
                (perm_move_left
                  (ofTree variableValues runtimeType branch.body).typeConditions
                  (frontierTypeConditions rest)
                  (ofTrees variableValues runtimeType
                    (CaseForest.selectedChildren possibleTypes variableValues rest)).typeConditions)
              simpa [ofBranches, ofTrees, CaseForest.selectedChildren,
                frontierTypeConditions, branchObservation, hcondition, hvalue, hselected,
                Trace.append, Trace.empty, List.append_assoc]
                using hfirst.trans hsecond
      | booleanLiteral literal =>
          simp only [hcondition] at hhead
          cases hvalue : booleanConditionAllows variableValues [literal] with
          | false =>
              have hselected : branchSelected variableValues runtimeType branch = false :=
                hhead.symm.trans hvalue
              simpa [ofBranches, ofTrees, CaseForest.selectedChildren,
                frontierTypeConditions, branchObservation, hcondition, hvalue,
                hselected, Trace.append, Trace.empty, List.append_assoc] using hih
          | true =>
              have hselected : branchSelected variableValues runtimeType branch = true :=
                hhead.symm.trans hvalue
              have hfirst := List.Perm.append_left
                (ofTree variableValues runtimeType branch.body).typeConditions hih
              have hsecond := perm_move_left
                (ofTree variableValues runtimeType branch.body).typeConditions
                (frontierTypeConditions rest)
                (ofTrees variableValues runtimeType
                  (CaseForest.selectedChildren possibleTypes variableValues rest)).typeConditions
              simpa [ofBranches, ofTrees, CaseForest.selectedChildren,
                frontierTypeConditions, branchObservation, hcondition, hvalue, hselected,
                Trace.append, Trace.empty, List.append_assoc]
                using hfirst.trans hsecond

private theorem ofBranches_booleanLiterals
    (variableValues : VariableValues) (runtimeType : Name)
    (possibleTypes : PossibleTypeRegion) (branches : List (Branch Tree))
    (htype
      : ∀ branch,
          branch ∈ branches
          -> match branch.condition with
              | .typeCondition _ =>
                  possibleTypesSubset possibleTypes branch.body.condition.possibleTypes
                  = branch.body.condition.possibleTypes.contains runtimeType
              | .booleanLiteral _ => True)
    : (ofBranches variableValues runtimeType branches).booleanLiterals.Perm
        (frontierBooleanLiterals variableValues branches
          ++ (ofTrees variableValues runtimeType
                (CaseForest.selectedChildren possibleTypes variableValues
                  branches)).booleanLiterals) := by
  induction branches with
  | nil => simp [ofBranches, ofTrees, CaseForest.selectedChildren,
      frontierBooleanLiterals, Trace.empty]
  | cons branch rest ih =>
      have hhead := branchSelection_eq variableValues runtimeType possibleTypes branch
        (htype branch (by simp))
      have hrest : ∀ candidate, candidate ∈ rest ->
          match candidate.condition with
          | .typeCondition _ =>
              possibleTypesSubset possibleTypes candidate.body.condition.possibleTypes
                = candidate.body.condition.possibleTypes.contains runtimeType
          | .booleanLiteral _ => True := by
        intro candidate hcandidate
        exact htype candidate (by simp [hcandidate])
      have hih := ih hrest
      cases hcondition : branch.condition with
      | typeCondition typeName =>
          simp only [hcondition] at hhead
          cases hvalue
                : possibleTypesSubset possibleTypes
                    branch.body.condition.possibleTypes with
          | false =>
              have hselected : branchSelected variableValues runtimeType branch = false :=
                hhead.symm.trans hvalue
              simpa [ofBranches, ofTrees, CaseForest.selectedChildren,
                frontierBooleanLiterals, branchObservation, hcondition, hvalue,
                hselected, Trace.append, Trace.empty, List.append_assoc] using hih
          | true =>
              have hselected : branchSelected variableValues runtimeType branch = true :=
                hhead.symm.trans hvalue
              have hfirst := List.Perm.append_left
                (ofTree variableValues runtimeType branch.body).booleanLiterals hih
              have hsecond := perm_move_left
                (ofTree variableValues runtimeType branch.body).booleanLiterals
                (frontierBooleanLiterals variableValues rest)
                (ofTrees variableValues runtimeType
                  (CaseForest.selectedChildren possibleTypes variableValues rest)).booleanLiterals
              simpa [ofBranches, ofTrees, CaseForest.selectedChildren,
                frontierBooleanLiterals, branchObservation, hcondition, hvalue, hselected,
                Trace.append, Trace.empty, List.append_assoc]
                using hfirst.trans hsecond
      | booleanLiteral literal =>
          simp only [hcondition] at hhead
          cases hvalue : booleanConditionAllows variableValues [literal] with
          | false =>
              have hselected : branchSelected variableValues runtimeType branch = false :=
                hhead.symm.trans hvalue
              simpa [ofBranches, ofTrees, CaseForest.selectedChildren,
                frontierBooleanLiterals, branchObservation, hcondition, hvalue, hselected,
                Trace.append, Trace.empty, List.append_assoc]
                using List.Perm.cons (selectedLiteral variableValues literal.variableName)
                  hih
          | true =>
              have hselected : branchSelected variableValues runtimeType branch = true :=
                hhead.symm.trans hvalue
              have hfirst := List.Perm.cons
                (selectedLiteral variableValues literal.variableName)
                (List.Perm.append_left
                  (ofTree variableValues runtimeType branch.body).booleanLiterals hih)
              have hsecond := List.Perm.cons
                (selectedLiteral variableValues literal.variableName)
                (perm_move_left
                  (ofTree variableValues runtimeType branch.body).booleanLiterals
                  (frontierBooleanLiterals variableValues rest)
                  (ofTrees variableValues runtimeType
                    (CaseForest.selectedChildren possibleTypes variableValues rest)).booleanLiterals)
              simpa [ofBranches, ofTrees, CaseForest.selectedChildren,
                frontierBooleanLiterals, branchObservation, hcondition, hvalue, hselected,
                Trace.append, Trace.empty, List.append_assoc]
                using hfirst.trans hsecond

private theorem ofTrees_namedFields
    (variableValues : VariableValues) (runtimeType : Name)
    (possibleTypes : PossibleTypeRegion) (trees : List Tree)
    (htype
      : ∀ tree,
          tree ∈ trees
          -> ∀ branch,
              branch ∈ tree.branches
              -> match branch.condition with
                  | .typeCondition _ =>
                      possibleTypesSubset possibleTypes
                        branch.body.condition.possibleTypes
                      = branch.body.condition.possibleTypes.contains runtimeType
                  | .booleanLiteral _ => True)
    : (ofTrees variableValues runtimeType trees).namedFields
      = (ofTrees variableValues runtimeType
          (CaseForest.resolveActiveTrees possibleTypes variableValues
            trees)).namedFields := by
  induction trees with
  | nil => simp [ofTrees, CaseForest.resolveActiveTrees, Trace.empty]
  | cons tree rest ih =>
      have hbranches := ofBranches_namedFields variableValues runtimeType possibleTypes
        tree.branches (htype tree (by simp))
      have hrest : ∀ candidate, candidate ∈ rest -> ∀ branch,
          branch ∈ candidate.branches ->
            match branch.condition with
            | .typeCondition _ =>
                possibleTypesSubset possibleTypes branch.body.condition.possibleTypes
                  = branch.body.condition.possibleTypes.contains runtimeType
            | .booleanLiteral _ => True := by
        intro candidate hcandidate
        exact htype candidate (by simp [hcandidate])
      have hih := ih hrest
      rw [ofTrees_cons, CaseForest.resolveActiveTrees, ofTrees_cons,
        ofTrees_append]
      simp only [ofTree, ofBranches, Trace.append, Trace.empty,
        CaseCursor.localNamedFields, List.nil_append, List.append_nil]
      change CaseCursor.localNamedFields tree ++
          (ofBranches variableValues runtimeType tree.branches).namedFields ++
          (ofTrees variableValues runtimeType rest).namedFields =
        CaseCursor.localNamedFields tree ++
          ((ofTrees variableValues runtimeType
              (CaseForest.selectedChildren possibleTypes variableValues
                tree.branches)).namedFields ++
            (ofTrees variableValues runtimeType
              (CaseForest.resolveActiveTrees possibleTypes variableValues rest)).namedFields)
      rw [hbranches, hih]
      simp [List.append_assoc]

private theorem ofTrees_typeConditions
    (variableValues : VariableValues) (runtimeType : Name)
    (possibleTypes : PossibleTypeRegion) (trees : List Tree)
    (htype
      : ∀ tree,
          tree ∈ trees
          -> ∀ branch,
              branch ∈ tree.branches
              -> match branch.condition with
                  | .typeCondition _ =>
                      possibleTypesSubset possibleTypes
                        branch.body.condition.possibleTypes
                      = branch.body.condition.possibleTypes.contains runtimeType
                  | .booleanLiteral _ => True)
    : (ofTrees variableValues runtimeType trees).typeConditions.Perm
        (frontierTypeConditions (trees.flatMap Tree.branches)
          ++ (ofTrees variableValues runtimeType
                (CaseForest.resolveActiveTrees possibleTypes variableValues
                  trees)).typeConditions) := by
  induction trees with
  | nil => simp [ofTrees, CaseForest.resolveActiveTrees, frontierTypeConditions,
      Trace.empty]
  | cons tree rest ih =>
      have hbranches := ofBranches_typeConditions variableValues runtimeType possibleTypes
        tree.branches (htype tree (by simp))
      have hrest : ∀ candidate, candidate ∈ rest -> ∀ branch,
          branch ∈ candidate.branches ->
            match branch.condition with
            | .typeCondition _ =>
                possibleTypesSubset possibleTypes branch.body.condition.possibleTypes
                  = branch.body.condition.possibleTypes.contains runtimeType
            | .booleanLiteral _ => True := by
        intro candidate hcandidate
        exact htype candidate (by simp [hcandidate])
      have hih := ih hrest
      have hfirst := hbranches.append hih
      have hsecond := List.Perm.append_left
        (frontierTypeConditions tree.branches)
        (perm_move_left
          (ofTrees variableValues runtimeType
            (CaseForest.selectedChildren possibleTypes variableValues tree.branches)).typeConditions
          (frontierTypeConditions (rest.flatMap Tree.branches))
          (ofTrees variableValues runtimeType
            (CaseForest.resolveActiveTrees possibleTypes variableValues rest)).typeConditions)
      have hfirst' :
          ((ofBranches variableValues runtimeType tree.branches).typeConditions ++
            (ofTrees variableValues runtimeType rest).typeConditions).Perm
            (frontierTypeConditions tree.branches ++
              ((ofTrees variableValues runtimeType
                  (CaseForest.selectedChildren possibleTypes variableValues
                    tree.branches)).typeConditions ++
                (frontierTypeConditions (rest.flatMap Tree.branches) ++
                  (ofTrees variableValues runtimeType
                    (CaseForest.resolveActiveTrees possibleTypes variableValues rest)).typeConditions))) := by
        simpa [List.append_assoc] using hfirst
      rw [ofTrees_cons, List.flatMap_cons, frontierTypeConditions_append,
        CaseForest.resolveActiveTrees, ofTrees_cons, ofTrees_append]
      simp only [ofTree, ofBranches, Trace.append, Trace.empty,
        List.nil_append]
      change ((ofBranches variableValues runtimeType tree.branches).typeConditions
              ++ (ofTrees variableValues runtimeType rest).typeConditions).Perm
              ((frontierTypeConditions tree.branches
                  ++ frontierTypeConditions (rest.flatMap Tree.branches))
                ++ ((ofTrees variableValues runtimeType
                      (CaseForest.selectedChildren possibleTypes variableValues
                        tree.branches)).typeConditions
                    ++ (ofTrees variableValues runtimeType
                          (CaseForest.resolveActiveTrees possibleTypes variableValues
                            rest)).typeConditions))
      simpa [List.append_assoc] using hfirst'.trans hsecond

private theorem ofTrees_booleanLiterals
    (variableValues : VariableValues) (runtimeType : Name)
    (possibleTypes : PossibleTypeRegion) (trees : List Tree)
    (htype
      : ∀ tree,
          tree ∈ trees
          -> ∀ branch,
              branch ∈ tree.branches
              -> match branch.condition with
                  | .typeCondition _ =>
                      possibleTypesSubset possibleTypes
                        branch.body.condition.possibleTypes
                      = branch.body.condition.possibleTypes.contains runtimeType
                  | .booleanLiteral _ => True)
    : (ofTrees variableValues runtimeType trees).booleanLiterals.Perm
        (frontierBooleanLiterals variableValues (trees.flatMap Tree.branches)
          ++ (ofTrees variableValues runtimeType
                (CaseForest.resolveActiveTrees possibleTypes variableValues
                  trees)).booleanLiterals) := by
  induction trees with
  | nil => simp [ofTrees, CaseForest.resolveActiveTrees, frontierBooleanLiterals,
      Trace.empty]
  | cons tree rest ih =>
      have hbranches := ofBranches_booleanLiterals variableValues runtimeType possibleTypes
        tree.branches (htype tree (by simp))
      have hrest : ∀ candidate, candidate ∈ rest -> ∀ branch,
          branch ∈ candidate.branches ->
            match branch.condition with
            | .typeCondition _ =>
                possibleTypesSubset possibleTypes branch.body.condition.possibleTypes
                  = branch.body.condition.possibleTypes.contains runtimeType
            | .booleanLiteral _ => True := by
        intro candidate hcandidate
        exact htype candidate (by simp [hcandidate])
      have hih := ih hrest
      have hfirst := hbranches.append hih
      have hsecond := List.Perm.append_left
        (frontierBooleanLiterals variableValues tree.branches)
        (perm_move_left
          (ofTrees variableValues runtimeType
            (CaseForest.selectedChildren possibleTypes variableValues tree.branches)).booleanLiterals
          (frontierBooleanLiterals variableValues (rest.flatMap Tree.branches))
          (ofTrees variableValues runtimeType
            (CaseForest.resolveActiveTrees possibleTypes variableValues rest)).booleanLiterals)
      have hfirst' :
          ((ofBranches variableValues runtimeType tree.branches).booleanLiterals ++
            (ofTrees variableValues runtimeType rest).booleanLiterals).Perm
            (frontierBooleanLiterals variableValues tree.branches ++
              ((ofTrees variableValues runtimeType
                  (CaseForest.selectedChildren possibleTypes variableValues
                    tree.branches)).booleanLiterals ++
                (frontierBooleanLiterals variableValues
                    (rest.flatMap Tree.branches) ++
                  (ofTrees variableValues runtimeType
                    (CaseForest.resolveActiveTrees possibleTypes variableValues rest)).booleanLiterals))) := by
        simpa [List.append_assoc] using hfirst
      rw [ofTrees_cons, List.flatMap_cons, frontierBooleanLiterals_append,
        CaseForest.resolveActiveTrees, ofTrees_cons, ofTrees_append]
      simp only [ofTree, ofBranches, Trace.append, Trace.empty,
        List.nil_append]
      change ((ofBranches variableValues runtimeType tree.branches).booleanLiterals
              ++ (ofTrees variableValues runtimeType rest).booleanLiterals).Perm
              ((frontierBooleanLiterals variableValues tree.branches
                  ++ frontierBooleanLiterals variableValues (rest.flatMap Tree.branches))
                ++ ((ofTrees variableValues runtimeType
                      (CaseForest.selectedChildren possibleTypes variableValues
                        tree.branches)).booleanLiterals
                    ++ (ofTrees variableValues runtimeType
                          (CaseForest.resolveActiveTrees possibleTypes variableValues
                            rest)).booleanLiterals))
      simpa [List.append_assoc] using hfirst'.trans hsecond

private theorem branch_type_selection_eq
    (forest : CaseForest) (region : PossibleTypeRegion)
    (hregion : region ∈ forest.typeRegions scope)
    (runtimeType : Name) (hruntime : runtimeType ∈ region)
    (tree : Tree) (htree : tree ∈ forest.activeTrees)
    (branch : Branch Tree) (hbranch : branch ∈ tree.branches)
    : match branch.condition with
      | .typeCondition _ =>
          possibleTypesSubset region branch.body.condition.possibleTypes
          = branch.body.condition.possibleTypes.contains runtimeType
      | .booleanLiteral _ => True := by
  cases hcondition : branch.condition with
  | booleanLiteral literal => trivial
  | typeCondition typeName =>
      have hforestBranch : branch ∈ forest.branches := by
        unfold CaseForest.branches
        exact List.mem_flatMap.mpr ⟨tree, htree, hbranch⟩
      have hallowed : branch.body.condition.possibleTypes ∈
          forest.typeBranchPossibleTypes := by
        unfold CaseForest.typeBranchPossibleTypes
        rw [List.mem_filterMap]
        exact ⟨branch, hforestBranch, by simp [hcondition]⟩
      exact possibleTypesSubset_eq_contains_of_constant region
        branch.body.condition.possibleTypes runtimeType hruntime
        (fun candidate hcandidate =>
          typeRegions_uniform forest scope region hregion candidate
            hcandidate runtimeType hruntime branch.body.condition.possibleTypes hallowed)

theorem resolveBranches_namedFields
    (forest : CaseForest) (scope region : PossibleTypeRegion)
    (hregion : region ∈ forest.typeRegions scope)
    (runtimeType : Name) (hruntime : runtimeType ∈ region)
    (variableValues : VariableValues)
    : (ofForest variableValues runtimeType forest).namedFields
      = (ofForest variableValues runtimeType
          (forest.resolveBranches region variableValues)).namedFields := by
  apply ofTrees_namedFields variableValues runtimeType region forest.activeTrees
  intro tree htree branch hbranch
  exact branch_type_selection_eq forest region hregion runtimeType hruntime
    tree htree branch hbranch

theorem resolveBranches_typeConditions
    (forest : CaseForest) (scope region : PossibleTypeRegion)
    (hregion : region ∈ forest.typeRegions scope)
    (runtimeType : Name) (hruntime : runtimeType ∈ region)
    (variableValues : VariableValues)
    : (ofForest variableValues runtimeType forest).typeConditions.Perm
        (frontierTypeConditions forest.branches
          ++ (ofForest variableValues runtimeType
                (forest.resolveBranches region variableValues)).typeConditions) := by
  apply ofTrees_typeConditions variableValues runtimeType region forest.activeTrees
  intro tree htree branch hbranch
  exact branch_type_selection_eq forest region hregion runtimeType hruntime
    tree htree branch hbranch

theorem resolveBranches_booleanLiterals
    (forest : CaseForest) (scope region : PossibleTypeRegion)
    (hregion : region ∈ forest.typeRegions scope)
    (runtimeType : Name) (hruntime : runtimeType ∈ region)
    (variableValues : VariableValues)
    : (ofForest variableValues runtimeType forest).booleanLiterals.Perm
        (frontierBooleanLiterals variableValues forest.branches
          ++ (ofForest variableValues runtimeType
                (forest.resolveBranches region variableValues)).booleanLiterals) := by
  apply ofTrees_booleanLiterals variableValues runtimeType region forest.activeTrees
  intro tree htree branch hbranch
  exact branch_type_selection_eq forest region hregion runtimeType hruntime
    tree htree branch hbranch

theorem frontierTypeConditions_eq (forest : CaseForest)
    : frontierTypeConditions forest.branches = forest.typeBranchPossibleTypes := by
  unfold CaseForest.typeBranchPossibleTypes
  induction forest.branches with
  | nil => rfl
  | cons branch rest ih =>
      cases hcondition : branch.condition <;>
        simp [frontierTypeConditions, hcondition, ih]

private theorem frontierTypeConditions_mem_ofBranches
    (variableValues : VariableValues) (runtimeType : Name)
    (branches : List (Branch Tree)) (allowed : PossibleTypes)
    (hallowed : allowed ∈ frontierTypeConditions branches)
    : allowed ∈ (ofBranches variableValues runtimeType branches).typeConditions := by
  induction branches with
  | nil => simp [frontierTypeConditions] at hallowed
  | cons branch rest ih =>
      cases hcondition : branch.condition with
      | typeCondition typeName =>
          simp only [frontierTypeConditions, hcondition, List.mem_cons] at hallowed
          rcases hallowed with rfl | hrest
          · simp [ofBranches, branchObservation, hcondition, Trace.append]
          · simp [ofBranches, branchObservation, hcondition, Trace.append, ih hrest]
      | booleanLiteral literal =>
          simp only [frontierTypeConditions, hcondition] at hallowed
          cases hselected : branchSelected variableValues runtimeType branch <;>
            simp [ofBranches, branchObservation, hcondition, hselected, Trace.append,
              ih hallowed]

private theorem frontierTypeConditions_mem_ofTrees
    (variableValues : VariableValues) (runtimeType : Name)
    (trees : List Tree) (allowed : PossibleTypes)
    (hallowed : allowed ∈ frontierTypeConditions (trees.flatMap Tree.branches))
    : allowed ∈ (ofTrees variableValues runtimeType trees).typeConditions := by
  induction trees with
  | nil => simp [frontierTypeConditions] at hallowed
  | cons tree rest ih =>
      rw [List.flatMap_cons, frontierTypeConditions_append] at hallowed
      rw [ofTrees_cons]
      simp only [Trace.append, List.mem_append]
      rcases List.mem_append.mp hallowed with htree | hrest
      · exact Or.inl (by
          simp only [ofTree, Trace.append, List.nil_append]
          exact frontierTypeConditions_mem_ofBranches variableValues runtimeType
            tree.branches allowed htree)
      · exact Or.inr (ih hrest)

theorem resolveBranches_typeFree
    (forest : CaseForest) (possibleTypes : PossibleTypeRegion)
    (runtimeType : Name) (variableValues : VariableValues)
    (htypes : (ofForest variableValues runtimeType forest).typeConditions = [])
    : forest.typeBranchPossibleTypes = []
      ∧ (ofForest variableValues runtimeType forest).namedFields
        = (ofForest variableValues runtimeType
            (forest.resolveBranches possibleTypes variableValues)).namedFields
      ∧ (ofForest variableValues runtimeType
          (forest.resolveBranches possibleTypes variableValues)).typeConditions
        = []
      ∧ (ofForest variableValues runtimeType forest).booleanLiterals.Perm
          (frontierBooleanLiterals variableValues forest.branches
            ++ (ofForest variableValues runtimeType
                  (forest.resolveBranches possibleTypes
                    variableValues)).booleanLiterals) := by
  have hfrontier : frontierTypeConditions forest.branches = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro allowed hallowed
    have hmem : allowed ∈ (ofForest variableValues runtimeType forest).typeConditions := by
      exact frontierTypeConditions_mem_ofTrees variableValues runtimeType forest.activeTrees
        allowed hallowed
    simp [htypes] at hmem
  have htypeBranches : forest.typeBranchPossibleTypes = [] := by
    rw [← frontierTypeConditions_eq]
    exact hfrontier
  have htype : ∀ tree, tree ∈ forest.activeTrees -> ∀ branch,
      branch ∈ tree.branches ->
        match branch.condition with
        | .typeCondition _ =>
            possibleTypesSubset possibleTypes branch.body.condition.possibleTypes =
              branch.body.condition.possibleTypes.contains runtimeType
        | .booleanLiteral _ => True := by
    intro tree htree branch hbranch
    cases hcondition : branch.condition with
    | typeCondition typeName =>
        have hmem : branch.body.condition.possibleTypes ∈
            forest.typeBranchPossibleTypes := by
          unfold CaseForest.typeBranchPossibleTypes CaseForest.branches
          rw [List.filterMap_flatMap]
          exact List.mem_flatMap.mpr ⟨tree, htree, by
            exact List.mem_filterMap.mpr ⟨branch, hbranch, by simp [hcondition]⟩⟩
        rw [htypeBranches] at hmem
        contradiction
    | booleanLiteral literal => trivial
  have hnamed := ofTrees_namedFields variableValues runtimeType possibleTypes
    forest.activeTrees htype
  have htypesPerm := ofTrees_typeConditions variableValues runtimeType possibleTypes
    forest.activeTrees htype
  have hbooleans := ofTrees_booleanLiterals variableValues runtimeType possibleTypes
    forest.activeTrees htype
  have hnextTypes :
      (ofForest variableValues runtimeType
        (forest.resolveBranches possibleTypes variableValues)).typeConditions = [] := by
    have hfrontier' :
        frontierTypeConditions (forest.activeTrees.flatMap Tree.branches) = [] := by
      simpa [CaseForest.branches] using hfrontier
    change (ofTrees variableValues runtimeType
      (CaseForest.resolveActiveTrees possibleTypes variableValues
        forest.activeTrees)).typeConditions = []
    rw [hfrontier', List.nil_append] at htypesPerm
    change (ofTrees variableValues runtimeType forest.activeTrees).typeConditions = [] at htypes
    rw [htypes] at htypesPerm
    exact (List.Perm.nil_eq htypesPerm).symm
  exact ⟨
    htypeBranches,
    by simpa [ofForest, CaseForest.resolveBranches] using hnamed,
    hnextTypes,
    by simpa [ofForest, CaseForest.resolveBranches, CaseForest.branches] using hbooleans
  ⟩

private theorem frontierBooleanLiterals_eq_map
    (variableValues : VariableValues) (branches : List (Branch Tree))
    : frontierBooleanLiterals variableValues branches
      = (frontierBooleanVariables branches).map (selectedLiteral variableValues) := by
  induction branches with
  | nil => rfl
  | cons branch rest ih =>
      cases hcondition : branch.condition <;>
        simp [frontierBooleanLiterals, frontierBooleanVariables, hcondition, ih]

private theorem frontierBooleanVariables_eq (forest : CaseForest)
    : frontierBooleanVariables forest.branches
      = (forest.branches.filterMap
          fun branch =>
            match branch.condition with
            | .typeCondition _ => none
            | .booleanLiteral literal => some literal.variableName) := by
  induction forest.branches with
  | nil => rfl
  | cons branch rest ih =>
      cases hcondition : branch.condition <;>
        simp [frontierBooleanVariables, hcondition, ih]

theorem frontierBooleanLiterals_mem_iff
    (variableValues : VariableValues) (forest : CaseForest)
    (literal : BooleanLiteral)
    : literal ∈ frontierBooleanLiterals variableValues forest.branches
      ↔ literal ∈ forest.booleanVariables.map (selectedLiteral variableValues) := by
  rw [frontierBooleanLiterals_eq_map, frontierBooleanVariables_eq]
  unfold CaseForest.booleanVariables
  simp
  rfl

theorem ofForest_branchless
    (variableValues : VariableValues) (runtimeType : Name) (forest : CaseForest)
    (hbranches : forest.hasUnresolvedBranches = false)
    : (ofForest variableValues runtimeType forest).namedFields = forest.namedFields
      ∧ (ofForest variableValues runtimeType forest).typeConditions = []
      ∧ (ofForest variableValues runtimeType forest).booleanLiterals = [] := by
  unfold CaseForest.hasUnresolvedBranches at hbranches
  have htreeBranches : ∀ tree, tree ∈ forest.activeTrees -> tree.branches = [] := by
    intro tree htree
    have hitem := List.any_eq_false.mp hbranches tree htree
    simpa using hitem
  unfold ofForest CaseForest.namedFields
  have aux : ∀ trees : List Tree,
      (∀ tree, tree ∈ trees -> tree.branches = []) ->
      (ofTrees variableValues runtimeType trees).namedFields =
          trees.flatMap (fun tree => tree.fields.flatMap fun group =>
            group.fields.map fun field => { responseName := group.responseName, field })
        ∧ (ofTrees variableValues runtimeType trees).typeConditions = []
        ∧ (ofTrees variableValues runtimeType trees).booleanLiterals = [] := by
    intro trees hall
    induction trees with
    | nil => simp [ofTrees, Trace.empty]
    | cons tree rest ih =>
        have htree := hall tree List.mem_cons_self
        have hrest : ∀ candidate, candidate ∈ rest -> candidate.branches = [] := by
          intro candidate hcandidate
          exact hall candidate (List.mem_cons_of_mem tree hcandidate)
        have hih := ih hrest
        rcases hih with ⟨hfields, htypes, hbooleans⟩
        rw [ofTrees_cons]
        simp only [ofTree, ofBranches, htree, Trace.append, Trace.empty,
          List.nil_append, List.append_nil]
        rw [hfields, htypes, hbooleans]
        simp [CaseCursor.localNamedFields]
  exact aux forest.activeTrees htreeBranches

end CaseTrace
end ExactCases
end TreeSummary
end GraphQL
