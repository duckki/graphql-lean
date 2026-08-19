import Proofs.GraphQL.Theories.ConditionTree.BooleanVariables
import Proofs.GraphQL.Theories.TreeSummary.ExactCases.BooleanDecision
import Proofs.GraphQL.Theories.TreeSummary.ExactCases.Relation
import Proofs.GraphQL.Theories.TreeSummary.ExactCases.ResolvedContext

/-! Refinement from a concrete Boolean environment to the unknown-variable summary. -/

namespace GraphQL
namespace TreeSummary
namespace ExactCases

open GraphQL.Execution
open GraphQL.ConditionTree
open GraphQL.ConditionTree.Termination
open TreeSummary.Measure
open Measure

private def BooleanValuesAgreeOn (variables : List Name) (left right : VariableValues)
    : Prop :=
  ∀ variableName,
    variableName ∈ variables
    -> inputValueBoolean? left (.variable variableName)
        = inputValueBoolean? right (.variable variableName)

private theorem booleanConditionAllows_eq_of_agree
    (left right : VariableValues) (literal : BooleanLiteral)
    (hagrees
      : inputValueBoolean? left (.variable literal.variableName)
        = inputValueBoolean? right (.variable literal.variableName))
    : booleanConditionAllows left [literal] = booleanConditionAllows right [literal] := by
  cases literal <;>
    simp_all [booleanConditionAllows, BooleanLiteral.allows,
      directiveAllowsSelectionBool, BooleanLiteral.toDirective,
      BooleanLiteral.variableName]

private theorem selectedChildren_eq_of_agree
    (possibleTypes : PossibleTypeRegion) (left right : VariableValues)
    (branches : List (Branch Tree))
    (hagrees
      : ∀ branch,
          branch ∈ branches
          -> match branch.condition with
              | .typeCondition _typeName => True
              | .booleanLiteral literal =>
                  inputValueBoolean? left (.variable literal.variableName)
                  = inputValueBoolean? right (.variable literal.variableName))
    : CaseForest.selectedChildren possibleTypes left branches
      = CaseForest.selectedChildren possibleTypes right branches := by
  induction branches with
  | nil => rfl
  | cons branch rest ih =>
      rw [CaseForest.selectedChildren, CaseForest.selectedChildren]
      have hrest := ih (by
        intro candidate hcandidate
        exact hagrees candidate (by simp [hcandidate]))
      cases hcondition : branch.condition with
      | typeCondition typeName => simp [hrest]
      | booleanLiteral literal =>
          have hvalue := hagrees branch (by simp)
          rw [hcondition] at hvalue
          simp only
          rw [booleanConditionAllows_eq_of_agree left right literal hvalue, hrest]

private theorem resolveActiveTrees_eq_of_agree
    (possibleTypes : PossibleTypeRegion) (left right : VariableValues)
    (items : List Tree)
    (hagrees
      : ∀ item,
          item ∈ items
          -> ∀ branch,
              branch ∈ item.branches
              -> match branch.condition with
                  | .typeCondition _typeName => True
                  | .booleanLiteral literal =>
                      inputValueBoolean? left (.variable literal.variableName)
                      = inputValueBoolean? right (.variable literal.variableName))
    : CaseForest.resolveActiveTrees possibleTypes left items
      = CaseForest.resolveActiveTrees possibleTypes right items := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      rw [CaseForest.resolveActiveTrees, CaseForest.resolveActiveTrees]
      rw [selectedChildren_eq_of_agree possibleTypes left right item.branches
        (hagrees item (by simp))]
      rw [ih (by
        intro candidate hcandidate
        exact hagrees candidate (by simp [hcandidate]))]

private def CaseForest.BooleanVariablesWithin (variables : List Name) (tree : CaseForest)
    : Prop :=
  ∀ item,
    item ∈ tree.activeTrees
    -> ∀ variableName,
        variableName ∈ conditionTreeBooleanVariables item -> variableName ∈ variables

private theorem conditionTreeBranchesBooleanVariable_mem
    (branches : List (Branch Tree)) (branch : Branch Tree)
    (hbranch : branch ∈ branches) (literal : BooleanLiteral)
    (hcondition : branch.condition = .booleanLiteral literal)
    : literal.variableName ∈ conditionTreeBranchesBooleanVariables branches := by
  induction branches with
  | nil => simp at hbranch
  | cons current rest ih =>
      rw [conditionTreeBranchesBooleanVariables.eq_def]
      simp only [List.mem_cons] at hbranch
      rcases hbranch with rfl | hbranch
      · simp [hcondition]
      · simp only [List.mem_append]
        exact Or.inr (ih hbranch)

private theorem CaseForest.booleanVariable_mem_of_within
    (tree : CaseForest) (variables : List Name)
    (hwithin : tree.BooleanVariablesWithin variables)
    (variableName : Name) (hvariable : variableName ∈ tree.booleanVariables)
    : variableName ∈ variables := by
  unfold CaseForest.booleanVariables CaseForest.branches at hvariable
  simp only [List.mem_eraseDups, List.mem_filterMap, List.mem_flatMap] at hvariable
  rcases hvariable with ⟨branch, ⟨item, hitem, hbranch⟩, hcondition⟩
  cases hbranchCondition : branch.condition with
  | typeCondition typeName => simp [hbranchCondition] at hcondition
  | booleanLiteral literal =>
      simp [hbranchCondition] at hcondition
      subst variableName
      apply hwithin item hitem
      cases item with
      | mk condition fields branches =>
          simp only [conditionTreeBooleanVariables, List.mem_append]
          apply Or.inr
          exact conditionTreeBranchesBooleanVariable_mem branches branch hbranch literal
            hbranchCondition

private theorem selectedChildren_source
    (possibleTypes : PossibleTypeRegion) (variableValues : VariableValues)
    (branches : List (Branch Tree)) (child : Tree)
    (hchild : child ∈ CaseForest.selectedChildren possibleTypes variableValues branches)
    : ∃ branch, branch ∈ branches ∧ child = branch.body := by
  induction branches with
  | nil => simp [CaseForest.selectedChildren] at hchild
  | cons branch rest ih =>
      rw [CaseForest.selectedChildren] at hchild
      cases hcondition : branch.condition with
      | typeCondition typeName =>
          simp only [hcondition] at hchild
          split at hchild
          · simp only [List.mem_cons] at hchild
            rcases hchild with rfl | hchild
            · exact ⟨branch, by simp, rfl⟩
            · rcases ih hchild with ⟨source, hsource, rfl⟩
              exact ⟨source, by simp [hsource], rfl⟩
          · rcases ih hchild with ⟨source, hsource, rfl⟩
            exact ⟨source, by simp [hsource], rfl⟩
      | booleanLiteral literal =>
          simp only [hcondition] at hchild
          split at hchild
          · simp only [List.mem_cons] at hchild
            rcases hchild with rfl | hchild
            · exact ⟨branch, by simp, rfl⟩
            · rcases ih hchild with ⟨source, hsource, rfl⟩
              exact ⟨source, by simp [hsource], rfl⟩
          · rcases ih hchild with ⟨source, hsource, rfl⟩
            exact ⟨source, by simp [hsource], rfl⟩

private theorem conditionTreeBranches_bodyVariable_mem
    (branches : List (Branch Tree)) (branch : Branch Tree)
    (hbranch : branch ∈ branches) (variableName : Name)
    (hvariable : variableName ∈ conditionTreeBooleanVariables branch.body)
    : variableName ∈ conditionTreeBranchesBooleanVariables branches := by
  induction branches with
  | nil => simp at hbranch
  | cons current rest ih =>
      rw [conditionTreeBranchesBooleanVariables.eq_def]
      simp only [List.mem_cons] at hbranch
      simp only [List.mem_append]
      rcases hbranch with rfl | hbranch
      · exact Or.inl (Or.inr hvariable)
      · exact Or.inr (ih hbranch)

private theorem resolveActiveTrees_variablesWithin
    (possibleTypes : PossibleTypeRegion) (variableValues : VariableValues)
    (items : List Tree) (variables : List Name)
    (hwithin
      : ∀ item,
          item ∈ items
          -> ∀ variableName,
              variableName ∈ conditionTreeBooleanVariables item
              -> variableName ∈ variables)
    : ∀ item,
        item ∈ CaseForest.resolveActiveTrees possibleTypes variableValues items
        -> ∀ variableName,
            variableName ∈ conditionTreeBooleanVariables item
            -> variableName ∈ variables := by
  induction items with
  | nil => simp [CaseForest.resolveActiveTrees]
  | cons source rest ih =>
      rw [CaseForest.resolveActiveTrees]
      intro item hitem variableName hvariable
      simp only [List.mem_cons, List.mem_append] at hitem
      rcases hitem with hitem | hitem | hitem
      · subst item
        apply hwithin source (by simp)
        cases source with
        | mk condition fields branches =>
            simp only [conditionTreeBooleanVariables, List.mem_append] at hvariable ⊢
            have hfields : variableName ∈ fields.flatMap
                (fun group => group.fields.flatMap
                  fun field =>
                    SelectionConditions.selectionSetBooleanVariables field.selectionSet) := by
              simpa [conditionTreeBranchesBooleanVariables] using hvariable
            exact Or.inl hfields
      · rcases selectedChildren_source possibleTypes variableValues source.branches
          item hitem with ⟨branch, hbranch, rfl⟩
        apply hwithin source (by simp)
        cases source with
        | mk condition fields branches =>
            simp only [conditionTreeBooleanVariables, List.mem_append]
            exact Or.inr
              (conditionTreeBranches_bodyVariable_mem branches branch hbranch variableName
                hvariable)
      · exact ih (by
          intro candidate hcandidate
          exact hwithin candidate (by simp [hcandidate])) item hitem variableName hvariable

private theorem CaseForest.resolveBranches_variablesWithin
    (possibleTypes : PossibleTypeRegion) (variableValues : VariableValues)
    (tree : CaseForest) (variables : List Name)
    (hwithin : tree.BooleanVariablesWithin variables)
    : (tree.resolveBranches possibleTypes variableValues).BooleanVariablesWithin
        variables := by
  intro item hitem variableName hvariable
  exact resolveActiveTrees_variablesWithin possibleTypes variableValues tree.activeTrees
    variables hwithin item hitem variableName hvariable

private theorem selectionSetBooleanVariables_append (left right : List Selection)
    : SelectionConditions.selectionSetBooleanVariables (left ++ right)
      = SelectionConditions.selectionSetBooleanVariables left
        ++ SelectionConditions.selectionSetBooleanVariables right := by
  induction left with
  | nil => rfl
  | cons selection rest tail_ih =>
      simp only [List.cons_append, SelectionConditions.selectionSetBooleanVariables, tail_ih,
        List.append_assoc]

private theorem mergeSelectionSets_eq_flatMap (selections : List Selection)
    : SelectionSet.mergeSelectionSets selections
      = selections.flatMap Selection.subselections :=
  rfl

private theorem mergedSelectionSet_variable_source
    (selections : List Selection) (variableName : Name)
    (hvariable
      : variableName
        ∈ SelectionConditions.selectionSetBooleanVariables
            (SelectionSet.mergeSelectionSets selections))
    : ∃ selection,
        selection ∈ selections
        ∧ variableName ∈ SelectionConditions.selectionBooleanVariables selection := by
  rw [mergeSelectionSets_eq_flatMap] at hvariable
  induction selections with
  | nil => simp [SelectionConditions.selectionSetBooleanVariables] at hvariable
  | cons selection rest ih =>
      simp only [List.flatMap_cons, selectionSetBooleanVariables_append,
        List.mem_append] at hvariable
      rcases hvariable with hhead | htail
      · exact ⟨selection, by simp, by
          cases selection <;>
            exact List.mem_append.mpr (Or.inr hhead)⟩
      · rcases ih htail with ⟨source, hsource, hsourceVariable⟩
        exact ⟨source, by simp [hsource], hsourceVariable⟩

private theorem collectFieldGroups_selections_source
    (fields : List NamedField) (selection : Selection)
    (hselection
      : selection
        ∈ (ConditionTree.collectFieldGroups fields).flatMap FieldGroup.selections)
    : ∃ field, field ∈ fields ∧ selection = field.toSelection := by
  unfold ConditionTree.collectFieldGroups at hselection
  have hfold : ∀ (rest : List NamedField) (groups : List FieldGroup),
      selection ∈ ((rest.foldl
          (fun current field => addFieldToGroups field current) groups).flatMap
            FieldGroup.selections)
      -> selection ∈ groups.flatMap FieldGroup.selections
        ∨ ∃ field, field ∈ rest ∧ selection = field.toSelection := by
    intro rest groups hmember
    induction rest generalizing groups with
    | nil => exact Or.inl hmember
    | cons field tail ih =>
        rw [List.foldl_cons] at hmember
        rcases ih (addFieldToGroups field groups) hmember with hadded | htail
        · rw [mem_groupedSelections_addField] at hadded
          rcases hadded with hfield | hgroup
          · exact Or.inr ⟨field, by simp, hfield⟩
          · exact Or.inl hgroup
        · rcases htail with ⟨source, hsource, heq⟩
          exact Or.inr ⟨source, by simp [hsource], heq⟩
  rcases hfold fields [] hselection with hnil | hsource
  · simp at hnil
  · exact hsource

private theorem CaseForest.namedField_variable_mem_of_within
    (tree : CaseForest) (variables : List Name)
    (hwithin : tree.BooleanVariablesWithin variables)
    (field : NamedField) (hfield : field ∈ tree.namedFields)
    (variableName : Name)
    (hvariable
      : variableName
        ∈ SelectionConditions.selectionSetBooleanVariables field.field.selectionSet)
    : variableName ∈ variables := by
  unfold CaseForest.namedFields at hfield
  simp only [List.mem_flatMap, List.mem_map] at hfield
  rcases hfield with ⟨item, hitem, group, hgroup, source, hsource, rfl⟩
  apply hwithin item hitem
  cases item with
  | mk condition fields branches =>
      simp only [conditionTreeBooleanVariables, List.mem_append]
      apply Or.inl
      apply List.mem_flatMap.mpr
      refine ⟨group, hgroup, ?_⟩
      apply List.mem_flatMap.mpr
      exact ⟨source, hsource, hvariable⟩

private theorem CaseForest.fieldGroup_variablesWithin
    (tree : CaseForest) (variables : List Name)
    (hwithin : tree.BooleanVariablesWithin variables)
    (inheritedBooleanCondition : List BooleanLiteral)
    (possibleTypes : PossibleTypeRegion) (group : CollectedFieldGroup)
    (hgroup : group ∈ tree.fieldGroups inheritedBooleanCondition possibleTypes)
    (variableName : Name)
    (hvariable
      : variableName
        ∈ SelectionConditions.selectionSetBooleanVariables group.mergedSelectionSet)
    : variableName ∈ variables := by
  unfold CaseForest.fieldGroups TreeSummary.collectFieldGroups at hgroup
  rcases List.mem_map.mp hgroup with ⟨sourceGroup, hsourceGroup, rfl⟩
  rcases mergedSelectionSet_variable_source sourceGroup.selections variableName
      hvariable with ⟨selection, hselection, hselectionVariable⟩
  have hselectionAll : selection ∈
      (ConditionTree.collectFieldGroups tree.namedFields).flatMap
        FieldGroup.selections := by
    exact List.mem_flatMap.mpr ⟨sourceGroup, hsourceGroup, hselection⟩
  rcases collectFieldGroups_selections_source tree.namedFields selection hselectionAll with
    ⟨field, hfield, rfl⟩
  cases field with
  | mk responseName sourceField =>
      apply tree.namedField_variable_mem_of_within variables hwithin
        { responseName := responseName, field := sourceField } hfield variableName
      simpa [NamedField.toSelection, Field.toSelection,
        SelectionConditions.selectionBooleanVariables] using hselectionVariable

private theorem assignedBooleanLiterals_eq_of_agree
    (variables : List Name) (left right : VariableValues)
    (hagrees : BooleanValuesAgreeOn variables left right)
    : variables.filterMap
        (fun variableName => do
          let value ← inputValueBoolean? left (.variable variableName)
          pure
            (if value then
                BooleanLiteral.positive variableName
              else
                BooleanLiteral.negative variableName))
      = variables.filterMap
          (fun variableName => do
            let value ← inputValueBoolean? right (.variable variableName)
            pure
              (if value then
                  BooleanLiteral.positive variableName
                else
                  BooleanLiteral.negative variableName)) := by
  induction variables with
  | nil => rfl
  | cons variableName rest ih =>
      rw [List.filterMap_cons, List.filterMap_cons,
        hagrees variableName (by simp), ih (by
          intro candidate hcandidate
          exact hagrees candidate (by simp [hcandidate]))]

private theorem extendBooleanCondition_eq_of_agree
    (inheritedBooleanCondition : List BooleanLiteral)
    (variables : List Name) (left right : VariableValues)
    (hagrees : BooleanValuesAgreeOn variables left right)
    : extendBooleanCondition inheritedBooleanCondition variables left
      = extendBooleanCondition inheritedBooleanCondition variables right := by
  unfold extendBooleanCondition
  rw [assignedBooleanLiterals_eq_of_agree variables left right hagrees]

private def BooleanEnvironment.Realizes (environment : BooleanEnvironment)
    (variableOrder remainingVariables : BooleanVariableNames)
    (assignment : Name -> Bool) (variableValues : VariableValues)
    : Prop :=
  ∀ variableName,
    variableName ∈ variableOrder
    -> match environment.status? variableName with
        | some (.known value) =>
            inputValueBoolean? environment.variableValues (.variable variableName)
              = some value
            ∧ inputValueBoolean? variableValues (.variable variableName) = some value
        | some .missing =>
            inputValueBoolean? environment.variableValues (.variable variableName) = none
            ∧ inputValueBoolean? variableValues (.variable variableName) = none
        | some .unresolved =>
            variableName ∈ remainingVariables
            ∧ inputValueBoolean? variableValues (.variable variableName)
              = some (assignment variableName)
        | none => False

private theorem mem_erase_of_ne_of_mem {α : Type} [BEq α] [LawfulBEq α]
    {selected candidate : α} {items : List α}
    (hne : candidate ≠ selected) (hmem : candidate ∈ items)
    : candidate ∈ items.erase selected := by
  induction items with
  | nil => simp at hmem
  | cons head tail ih =>
      by_cases hhead : head = selected
      · subst head
        rw [List.erase_cons_head]
        rcases List.mem_cons.mp hmem with hsame | htail
        · exact False.elim (hne hsame)
        · exact htail
      · have htailErase : ¬(head == selected) = true := by
          rw [show (head == selected) = false from (beq_eq_false_iff_ne).2 hhead]
          decide
        rw [List.erase_cons_tail htailErase]
        rcases List.mem_cons.mp hmem with hsame | htail
        · exact List.mem_cons.mpr (Or.inl hsame)
        · exact List.mem_cons_of_mem head (ih htail)

private theorem BooleanEnvironment.Realizes.assign
    {environment : BooleanEnvironment}
    {variableOrder remainingVariables : BooleanVariableNames}
    {assignment : Name -> Bool} {variableValues : VariableValues}
    (hrealizes
      : environment.Realizes variableOrder remainingVariables assignment variableValues)
    (variableName : Name) (hvariable : variableName ∈ variableOrder)
    (hstatus : environment.status? variableName = some .unresolved)
    : (environment.assign variableName (assignment variableName)).Realizes
        variableOrder (remainingVariables.erase variableName) assignment
        variableValues := by
  intro candidate hcandidate
  by_cases heq : candidate = variableName
  · subst candidate
    have hvalue := hrealizes variableName hvariable
    simp only [hstatus] at hvalue
    simp only [BooleanEnvironment.assign, BooleanEnvironment.status?, List.lookup,
      beq_self_eq_true, ↓reduceIte, inputValueBoolean?, lookupVariableValue?,
      InputValue.staticBoolean?]
    exact ⟨rfl, hvalue.2⟩
  · have hne : variableName ≠ candidate := fun equal => heq equal.symm
    have hcandidateRealizes := hrealizes candidate hcandidate
    have hstatusEq :
        (environment.assign variableName (assignment variableName)).status? candidate
          = environment.status? candidate := by
      unfold BooleanEnvironment.assign BooleanEnvironment.status?
      simp only [List.lookup]
      rw [show (candidate == variableName) = false from
        (beq_eq_false_iff_ne).2 heq]
    have hinputEq :
        inputValueBoolean?
            (environment.assign variableName (assignment variableName)).variableValues
            (.variable candidate)
          = inputValueBoolean? environment.variableValues (.variable candidate) := by
      simp only [BooleanEnvironment.assign, inputValueBoolean?, lookupVariableValue?]
      rw [if_neg hne]
    rw [hstatusEq]
    cases hcandidateStatus : environment.status? candidate with
    | none => simp [hcandidateStatus] at hcandidateRealizes
    | some status =>
        cases status with
        | known value =>
            simp only [hcandidateStatus] at hcandidateRealizes
            rw [hinputEq]
            exact hcandidateRealizes
        | missing =>
            simp only [hcandidateStatus] at hcandidateRealizes
            rw [hinputEq]
            exact hcandidateRealizes
        | unresolved =>
            simp only [hcandidateStatus] at hcandidateRealizes
            exact ⟨mem_erase_of_ne_of_mem heq hcandidateRealizes.1,
              hcandidateRealizes.2⟩

private theorem BooleanEnvironment.Realizes.agreesOn
    {environment : BooleanEnvironment}
    {variableOrder remainingVariables localVariables : BooleanVariableNames}
    {assignment : Name -> Bool} {variableValues : VariableValues}
    (hrealizes
      : environment.Realizes variableOrder remainingVariables assignment variableValues)
    (hlocal
      : ∀ variableName, variableName ∈ localVariables -> variableName ∈ variableOrder)
    (hnext : environment.nextUnresolved remainingVariables localVariables = none)
    : BooleanValuesAgreeOn localVariables environment.variableValues variableValues := by
  intro variableName hvariable
  have hreal := hrealizes variableName (hlocal variableName hvariable)
  cases hstatus : environment.status? variableName with
  | none => simp [hstatus] at hreal
  | some status =>
      cases status with
      | known value =>
          simp only [hstatus] at hreal
          exact hreal.1.trans hreal.2.symm
      | missing =>
          simp only [hstatus] at hreal
          exact hreal.1.trans hreal.2.symm
      | unresolved =>
          simp only [hstatus] at hreal
          have hnot := (List.find?_eq_none.mp hnext) variableName hreal.1
          simp [hvariable, hstatus] at hnot

private def realizationSummarizePhase : Nat := 3
private def realizationTypeRegionsPhase : Nat := 2
private def realizationFieldGroupsPhase : Nat := 1
private def realizationChildTypesPhase : Nat := 0

private def realizationControlCount (tree : CaseForest)
    (remainingVariables : BooleanVariableNames)
    : Nat :=
  caseForestUnresolvedCount tree + remainingVariables.length

private theorem CaseForest.resolveBranches_eq_of_agreeBooleanVariables
    (possibleTypes : PossibleTypeRegion) (left right : VariableValues)
    (tree : CaseForest)
    (hagrees : BooleanValuesAgreeOn tree.booleanVariables left right)
    : tree.resolveBranches possibleTypes left
      = tree.resolveBranches possibleTypes right := by
  apply congrArg CaseForest.mk
  apply resolveActiveTrees_eq_of_agree
  intro item hitem branch hbranch
  cases hcondition : branch.condition with
  | typeCondition typeName => trivial
  | booleanLiteral literal =>
      apply hagrees literal.variableName
      unfold CaseForest.booleanVariables CaseForest.branches
      simp only [List.mem_eraseDups, List.mem_filterMap, List.mem_flatMap]
      exact ⟨branch, ⟨item, hitem, hbranch⟩, by simp [hcondition]⟩

mutual
  private theorem CaseForest.summarizeDecision_evaluate_eq
      (algebra : Algebra) (schema : Schema)
      (variableOrder remainingVariables : BooleanVariableNames)
      (assignment : Name -> Bool) (environment : BooleanEnvironment)
      (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
      (tree : CaseForest) (possibleTypes : PossibleTypeRegion)
      (variableValues : VariableValues)
      (hwithin : tree.BooleanVariablesWithin variableOrder)
      (hrealizes
        : environment.Realizes variableOrder remainingVariables assignment variableValues)
      : (summarizeDecision algebra schema variableOrder remainingVariables parentType
          inheritedBooleanCondition tree possibleTypes environment).evaluate
          assignment
        = summarize algebra schema parentType inheritedBooleanCondition tree possibleTypes
            variableValues environment.fixedVariableValues := by
    rw [summarizeDecision, summarize]
    split <;> rename_i hbranches
    · cases hnext
            : environment.nextUnresolved remainingVariables tree.booleanVariables with
      | some variableName =>
          simp only [BooleanDecision.evaluate]
          have hremaining := List.mem_of_find?_eq_some hnext
          have hselected := List.find?_some hnext
          change
            (variableName ∈ tree.booleanVariables
              && match environment.status? variableName with
                | some .missing | some (.known _value) => false
                | some .unresolved | none => true) = true at hselected
          simp only [Bool.and_eq_true] at hselected
          have hvariable :=
            tree.booleanVariable_mem_of_within variableOrder hwithin variableName
              (of_decide_eq_true hselected.1)
          have hstatus : environment.status? variableName = some .unresolved := by
            have hreal := hrealizes variableName hvariable
            cases hstatus : environment.status? variableName with
            | none => simp [hstatus] at hreal
            | some status =>
                cases status <;> simp_all
          have hnextRealizes :=
            hrealizes.assign variableName hvariable hstatus
          by_cases hvalue : assignment variableName
          · simpa [hvalue, CaseForest.summarize, hbranches,
                BooleanEnvironment.assign] using
              summarizeDecision_evaluate_eq algebra schema variableOrder
                (remainingVariables.erase variableName) assignment
                (environment.assign variableName (assignment variableName)) parentType
                inheritedBooleanCondition tree possibleTypes variableValues hwithin
                hnextRealizes
          · simpa [hvalue, CaseForest.summarize, hbranches,
                BooleanEnvironment.assign] using
              summarizeDecision_evaluate_eq algebra schema variableOrder
                (remainingVariables.erase variableName) assignment
                (environment.assign variableName (assignment variableName)) parentType
                inheritedBooleanCondition tree possibleTypes variableValues hwithin
                hnextRealizes
      | none =>
          simp only
          exact summarizeTypeRegionsDecision_evaluate_eq algebra schema variableOrder
            remainingVariables assignment environment parentType inheritedBooleanCondition
            tree (tree.typeRegions possibleTypes) variableValues hbranches hwithin
            hrealizes hnext
    · exact summarizeFieldGroupsDecision_evaluate_eq algebra schema variableOrder
        remainingVariables assignment environment
        (tree.fieldGroups inheritedBooleanCondition possibleTypes)
        variableValues hrealizes (by
          intro group hgroup variableName hvariable
          exact tree.fieldGroup_variablesWithin variableOrder hwithin
            inheritedBooleanCondition possibleTypes group hgroup variableName hvariable)
  termination_by
    (
      caseForestResponseDepth tree,
      realizationControlCount tree remainingVariables,
      realizationSummarizePhase,
      0
    )
  decreasing_by
    all_goals
      first
      | apply quadruple_lt_of_depth_le_of_control_lt
        · exact Nat.le_refl _
        · have hlength := List.length_erase_of_mem hremaining
          have hpositive := List.length_pos_of_mem hremaining
          unfold realizationControlCount
          rw [hlength]
          omega
      | apply quadruple_lt_of_depth_le_of_control_le_of_phase_lt
        · exact Nat.le_refl _
        · exact Nat.le_refl _
        · decide
      | apply quadruple_lt_of_depth_le_of_control_le_of_phase_lt
        · exact fieldGroupsResponseDepth_le inheritedBooleanCondition
            possibleTypes tree
        · unfold realizationControlCount
          omega
        · decide

  private theorem CaseForest.summarizeTypeRegionsDecision_evaluate_eq
      (algebra : Algebra) (schema : Schema)
      (variableOrder remainingVariables : BooleanVariableNames)
      (assignment : Name -> Bool) (environment : BooleanEnvironment)
      (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
      (tree : CaseForest) (regions : List PossibleTypeRegion)
      (variableValues : VariableValues)
      (hbranches : tree.hasUnresolvedBranches = true)
      (hwithin : tree.BooleanVariablesWithin variableOrder)
      (hrealizes
        : environment.Realizes variableOrder remainingVariables assignment variableValues)
      (hnext : environment.nextUnresolved remainingVariables tree.booleanVariables = none)
      : (summarizeTypeRegionsDecision algebra schema variableOrder remainingVariables
          parentType inheritedBooleanCondition tree regions environment
          hbranches).evaluate
          assignment
        = summarizeTypeRegions algebra schema parentType inheritedBooleanCondition tree
            regions variableValues hbranches environment.fixedVariableValues := by
    rw [summarizeTypeRegionsDecision, BooleanDecision.evaluate_joinMap]
    unfold summarizeTypeRegions
    apply congrArg (joinMap algebra regions)
    funext region hregion
    have hagrees := hrealizes.agreesOn
      (fun variableName hvariable =>
        tree.booleanVariable_mem_of_within variableOrder hwithin variableName hvariable)
      hnext
    have hinherited := extendBooleanCondition_eq_of_agree
      inheritedBooleanCondition tree.booleanVariables environment.variableValues
      variableValues hagrees
    have hresolved := tree.resolveBranches_eq_of_agreeBooleanVariables region
      environment.variableValues variableValues hagrees
    rw [hinherited, hresolved]
    exact summarizeDecision_evaluate_eq algebra schema variableOrder remainingVariables
      assignment environment parentType
      (extendBooleanCondition inheritedBooleanCondition tree.booleanVariables
        variableValues)
      (tree.resolveBranches region variableValues) region variableValues
      (tree.resolveBranches_variablesWithin region variableValues variableOrder hwithin)
      hrealizes
  termination_by
    (
      caseForestResponseDepth tree,
      realizationControlCount tree remainingVariables,
      realizationTypeRegionsPhase,
      sizeOf regions
    )
  decreasing_by
    apply quadruple_lt_of_depth_le_of_control_lt
    · exact resolveBranches_responseDepth_le region variableValues tree
    · have hcount := resolveBranches_unresolvedCount_lt region variableValues tree
        hbranches
      unfold realizationControlCount
      omega

  private theorem CaseForest.summarizeFieldGroupsDecision_evaluate_eq
      (algebra : Algebra) (schema : Schema)
      (variableOrder remainingVariables : BooleanVariableNames)
      (assignment : Name -> Bool) (environment : BooleanEnvironment)
      (groups : List CollectedFieldGroup) (variableValues : VariableValues)
      (hrealizes
        : environment.Realizes variableOrder remainingVariables assignment variableValues)
      (hgroups
        : ∀ group,
            group ∈ groups
            -> ∀ variableName,
                variableName
                  ∈ SelectionConditions.selectionSetBooleanVariables
                      group.mergedSelectionSet
                -> variableName ∈ variableOrder)
      : (summarizeFieldGroupsDecision algebra schema variableOrder remainingVariables
          groups environment).evaluate
          assignment
        = summarizeFieldGroups algebra schema groups variableValues
            environment.fixedVariableValues := by
    rw [summarizeFieldGroupsDecision, BooleanDecision.evaluate_combineMap]
    unfold summarizeFieldGroups
    apply congrArg (combineMap algebra groups)
    funext group hgroup
    rw [BooleanDecision.evaluate_map]
    apply congrArg (algebra.field group)
    exact summarizeChildTypesDecision_evaluate_eq algebra schema variableOrder
      remainingVariables assignment environment group (childParentTypes schema group)
      variableValues hrealizes (hgroups group hgroup)
  termination_by
    (
      collectedFieldGroupsResponseDepth groups,
      remainingVariables.length,
      realizationFieldGroupsPhase,
      sizeOf groups
    )
  decreasing_by
    apply quadruple_lt_of_depth_le_of_control_le_of_phase_lt
    · exact collectedFieldGroupResponseDepth_le_of_mem group groups hgroup
    · exact Nat.le_refl _
    · decide

  private theorem CaseForest.summarizeChildTypesDecision_evaluate_eq
      (algebra : Algebra) (schema : Schema)
      (variableOrder remainingVariables : BooleanVariableNames)
      (assignment : Name -> Bool) (environment : BooleanEnvironment)
      (group : CollectedFieldGroup) (parentTypes : TypeNames)
      (variableValues : VariableValues)
      (hrealizes
        : environment.Realizes variableOrder remainingVariables assignment variableValues)
      (hgroup
        : ∀ variableName,
            variableName
              ∈ SelectionConditions.selectionSetBooleanVariables group.mergedSelectionSet
            -> variableName ∈ variableOrder)
      : (summarizeChildTypesDecision algebra schema variableOrder remainingVariables
          group parentTypes environment).evaluate
          assignment
        = summarizeChildTypes algebra schema group parentTypes variableValues
            environment.fixedVariableValues := by
    rw [summarizeChildTypesDecision, BooleanDecision.evaluate_joinMap]
    unfold summarizeChildTypes
    apply congrArg (joinMap algebra parentTypes)
    funext childParentType hparentType
    let childTree := group.childTreeWithKnownFalsePruning schema childParentType
      environment.fixedVariableValues
    apply summarizeDecision_evaluate_eq algebra schema variableOrder remainingVariables
      assignment environment childParentType group.childInheritedBooleanCondition
      (.ofConditionTree childTree) childTree.condition.possibleTypes variableValues
    · intro item hitem variableName hvariable
      simp only [CaseForest.ofConditionTree, List.mem_singleton] at hitem
      subst item
      apply hgroup variableName
      exact ofSelectionSetInScopeWithKnownFalsePruning_booleanVariablesWithin schema
        childParentType group.childInheritedBooleanCondition
        environment.fixedVariableValues group.mergedSelectionSet variableName hvariable
    · exact hrealizes
  termination_by
    (
      collectedFieldGroupResponseDepth group,
      remainingVariables.length,
      realizationChildTypesPhase,
      sizeOf parentTypes
    )
  decreasing_by
    apply Prod.Lex.left
    have hchild := conditionTreeResponseDepth_ofSelectionSetInScopeWithKnownFalsePruning schema
      childParentType group.childInheritedBooleanCondition
      environment.fixedVariableValues group.mergedSelectionSet
    change conditionTreeResponseDepth childTree
      ≤ Termination.selectionSetResponseDepth group.mergedSelectionSet at hchild
    simp only [CaseForest.ofConditionTree, caseForestResponseDepth,
      activeTreesResponseDepth, Nat.max_zero]
    exact Nat.lt_of_le_of_lt hchild (Nat.lt_succ_self _)
end

private def BooleanEnvironment.prepareFor
    : BooleanVariableNames -> VariableValues -> BooleanEnvironment -> BooleanEnvironment
  | [], _variableValues, environment => environment
  | variableName :: rest, variableValues, environment =>
      let status :=
        match inputValueBoolean? variableValues (.variable variableName) with
        | some _value => .unresolved
        | none => .missing
      prepareFor rest variableValues (environment.withStatus variableName status)

private def assignmentFor (variableValues : VariableValues) (variableName : Name)
    : Bool :=
  (inputValueBoolean? variableValues (.variable variableName)).getD false

private theorem BooleanEnvironment.prepareFor_variableValues
    (variables : BooleanVariableNames) (variableValues : VariableValues)
    (environment : BooleanEnvironment)
    : (environment.prepareFor variables variableValues).variableValues
      = environment.variableValues := by
  induction variables generalizing environment with
  | nil => rfl
  | cons variableName rest ih =>
      rw [BooleanEnvironment.prepareFor]
      exact ih _

private theorem BooleanEnvironment.prepareFor_fixedVariableValues
    (variables : BooleanVariableNames) (variableValues : VariableValues)
    (environment : BooleanEnvironment)
    : (environment.prepareFor variables variableValues).fixedVariableValues
      = environment.fixedVariableValues := by
  induction variables generalizing environment with
  | nil => rfl
  | cons variableName rest ih =>
      rw [BooleanEnvironment.prepareFor]
      exact ih _

private theorem BooleanEnvironment.prepareFor_status?_of_not_mem
    (variables : BooleanVariableNames) (variableValues : VariableValues)
    (environment : BooleanEnvironment) (candidate : Name)
    (hnotMem : candidate ∉ variables)
    : (environment.prepareFor variables variableValues).status? candidate
      = environment.status? candidate := by
  induction variables generalizing environment with
  | nil => rfl
  | cons variableName rest ih =>
      simp only [List.mem_cons, not_or] at hnotMem
      rw [BooleanEnvironment.prepareFor, ih _ hnotMem.2]
      unfold BooleanEnvironment.withStatus BooleanEnvironment.status?
      simp only [List.lookup]
      rw [show (candidate == variableName) = false from
        (beq_eq_false_iff_ne).2 hnotMem.1]

private theorem BooleanEnvironment.prepareFor_status?_of_mem
    (variables : BooleanVariableNames) (variableValues : VariableValues)
    (environment : BooleanEnvironment) (candidate : Name)
    (hnodup : variables.Nodup) (hmem : candidate ∈ variables)
    : (environment.prepareFor variables variableValues).status? candidate
      = match inputValueBoolean? variableValues (.variable candidate) with
        | some _value => some .unresolved
        | none => some .missing := by
  induction variables generalizing environment with
  | nil => simp at hmem
  | cons variableName rest ih =>
      rw [BooleanEnvironment.prepareFor]
      simp only [List.nodup_cons] at hnodup
      rcases List.mem_cons.mp hmem with rfl | hmem
      · rw [BooleanEnvironment.prepareFor_status?_of_not_mem rest variableValues
          _ _ hnodup.1]
        unfold BooleanEnvironment.withStatus BooleanEnvironment.status?
        simp only [List.lookup, beq_self_eq_true]
        split <;> rfl
      · exact ih _ hnodup.2 hmem

private theorem BooleanEnvironment.prepareFor_realizes
    (variables : BooleanVariableNames) (variableValues : VariableValues)
    (hnodup : variables.Nodup)
    : BooleanEnvironment.unknown.prepareFor variables variableValues
      |>.Realizes variables variables (assignmentFor variableValues) variableValues := by
  intro variableName hvariable
  rw [BooleanEnvironment.prepareFor_status?_of_mem variables variableValues _
    variableName hnodup hvariable]
  rw [BooleanEnvironment.prepareFor_variableValues]
  cases hvalue : inputValueBoolean? variableValues (.variable variableName) with
  | none =>
      simp [BooleanEnvironment.unknown, inputValueBoolean?, lookupVariableValue?]
  | some value =>
      simp only [hvalue, assignmentFor, Option.getD_some]
      exact ⟨hvariable, True.intro⟩

private theorem BooleanDecision.evaluate_le_collapse
    (algebra : Algebra) (lawful : algebra.Lawful)
    (assignment : Name -> Bool) (decision : BooleanDecision algebra.Summary)
    : lawful.le (decision.evaluate assignment) (decision.collapse algebra) := by
  induction decision with
  | leaf summary => exact lawful.le_refl summary
  | split variableName onFalse onTrue ihFalse ihTrue =>
      by_cases hvalue : assignment variableName
      · simpa [BooleanDecision.evaluate, BooleanDecision.collapse, hvalue] using
          lawful.le_trans _ _ _ ihTrue (lawful.le_join_right _ _)
      · simpa [BooleanDecision.evaluate, BooleanDecision.collapse, hvalue] using
          lawful.le_trans _ _ _ ihFalse (lawful.le_join_left _ _)

private theorem BooleanEnvironment.prepareFor_le_summarizeCompletions
    (algebra : Algebra) (lawful : algebra.Lawful)
    (summarize : BooleanEnvironment -> algebra.Summary)
    (variables : BooleanVariableNames) (variableValues : VariableValues)
    (environment : BooleanEnvironment)
    (hnodup : variables.Nodup)
    (hemptyValues : environment.variableValues = [])
    (habsent
      : ∀ variableName,
          variableName ∈ variables -> environment.status? variableName = none)
    : lawful.le (summarize (environment.prepareFor variables variableValues))
        (environment.summarizeCompletions algebra summarize variables) := by
  induction variables generalizing environment with
  | nil =>
      simpa [BooleanEnvironment.prepareFor,
        BooleanEnvironment.summarizeCompletions] using
        lawful.le_refl (summarize environment)
  | cons variableName rest ih =>
      simp only [List.nodup_cons] at hnodup
      have hstatus := habsent variableName (by simp)
      have hinput : inputValueBoolean? environment.variableValues
          (.variable variableName) = none := by
        rw [hemptyValues]
        simp [inputValueBoolean?, lookupVariableValue?]
      have hlookup : lookupVariableValue? environment.variableValues variableName = none := by
        rw [hemptyValues]
        simp [lookupVariableValue?]
      have hrestAbsent (status : BooleanStatus) :
          ∀ candidate,
            candidate ∈ rest
            -> (environment.withStatus variableName status).status? candidate = none := by
        intro candidate hcandidate
        have hcandidateNe : candidate ≠ variableName := by
          intro heq
          subst candidate
          exact hnodup.1 hcandidate
        unfold BooleanEnvironment.withStatus BooleanEnvironment.status?
        simp only [List.lookup]
        rw [show (candidate == variableName) = false from
          (beq_eq_false_iff_ne).2 hcandidateNe]
        exact habsent candidate (by simp [hcandidate])
      rw [BooleanEnvironment.prepareFor,
        BooleanEnvironment.summarizeCompletions, hstatus, hinput, hlookup]
      cases hvalue : inputValueBoolean? variableValues (.variable variableName) with
      | none =>
          exact lawful.le_trans _ _ _
            (ih (environment.withStatus variableName .missing) hnodup.2
              hemptyValues (hrestAbsent .missing))
            (lawful.le_join_left _ _)
      | some value =>
          exact lawful.le_trans _ _ _
            (ih (environment.withStatus variableName .unresolved) hnodup.2
              hemptyValues (hrestAbsent .unresolved))
            (lawful.le_join_right _ _)

private theorem summarizeSelectionSetResolved_le_unknown
    (algebra : Algebra) (lawful : algebra.Lawful)
    (schema : Schema) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (selectionSet : List Selection) (variableValues : VariableValues)
    : lawful.le
        (summarizeSelectionSetResolved algebra schema parentType
          inheritedBooleanCondition selectionSet variableValues [])
        (summarizeSelectionSet algebra schema parentType inheritedBooleanCondition
          selectionSet BooleanEnvironment.unknown) := by
  let tree := ConditionTree.ofSelectionSetInScopeWithKnownFalsePruning schema parentType
    inheritedBooleanCondition [] selectionSet
  let variables := (conditionTreeBooleanVariables tree).eraseDups
  let initial : BooleanEnvironment := BooleanEnvironment.unknown
  let prepared := initial.prepareFor variables variableValues
  let assignment := assignmentFor variableValues
  have hwithin : (CaseForest.ofConditionTree tree).BooleanVariablesWithin variables := by
    intro item hitem variableName hvariable
    simp only [CaseForest.ofConditionTree, List.mem_singleton] at hitem
    subst item
    exact List.mem_eraseDups.mpr hvariable
  have hrealizes : prepared.Realizes variables variables assignment variableValues := by
    exact BooleanEnvironment.prepareFor_realizes variables variableValues
      (BooleanDecision.eraseDups_nodup _)
  have hevaluate :=
    CaseForest.summarizeDecision_evaluate_eq algebra schema variables variables assignment
      prepared parentType inheritedBooleanCondition (.ofConditionTree tree)
      tree.condition.possibleTypes variableValues hwithin hrealizes
  have hpreparedFixed : prepared.fixedVariableValues = [] := by
    rw [BooleanEnvironment.prepareFor_fixedVariableValues]
    rfl
  rw [hpreparedFixed] at hevaluate
  have hevaluateLe := BooleanDecision.evaluate_le_collapse algebra lawful assignment
    (CaseForest.summarizeDecision algebra schema variables variables parentType
      inheritedBooleanCondition (.ofConditionTree tree) tree.condition.possibleTypes
      prepared)
  have hprepared : lawful.le
      ((CaseForest.summarizeDecision algebra schema variables variables parentType
        inheritedBooleanCondition (.ofConditionTree tree) tree.condition.possibleTypes
        prepared).collapse algebra)
      (BooleanEnvironment.summarizeCompletions algebra
        (fun completed =>
          (CaseForest.summarizeDecision algebra schema variables variables parentType
            inheritedBooleanCondition (.ofConditionTree tree)
            tree.condition.possibleTypes completed).collapse algebra)
        variables initial) := by
    simpa [prepared] using
      (BooleanEnvironment.prepareFor_le_summarizeCompletions algebra lawful
        (fun completed =>
          (CaseForest.summarizeDecision algebra schema variables variables parentType
            inheritedBooleanCondition (.ofConditionTree tree)
            tree.condition.possibleTypes completed).collapse algebra)
        variables variableValues initial (BooleanDecision.eraseDups_nodup _) rfl
        (by intro variableName hvariable; rfl))
  unfold summarizeSelectionSetResolved summarizeConditionTreeResolved
    summarizeSelectionSet summarizeConditionTree summarizeConditionTreeDecision
  change lawful.le
    (CaseForest.summarize algebra schema parentType inheritedBooleanCondition
      (.ofConditionTree tree) tree.condition.possibleTypes variableValues [])
    (BooleanEnvironment.summarizeCompletions algebra
      (fun completed =>
        (CaseForest.summarizeDecision algebra schema variables variables parentType
          inheritedBooleanCondition (.ofConditionTree tree)
          tree.condition.possibleTypes completed).collapse algebra)
      variables initial)
  exact lawful.le_trans _ _ _ (hevaluate ▸ hevaluateLe) hprepared

theorem summarizeOperationResolved_le_unknown
    (algebra : Algebra) (lawful : algebra.Lawful) (schema : Schema)
    (operation : Operation) (variableValues : VariableValues)
    : lawful.le
        (summarizeSelectionSetResolved algebra schema (operation.rootType schema) []
          operation.selectionSet variableValues [])
        (summarizeOperation algebra schema operation) := by
  simpa [summarizeOperation, summarizeSelectionSet] using
    summarizeSelectionSetResolved_le_unknown algebra lawful schema
      (operation.rootType schema) [] operation.selectionSet variableValues

end ExactCases
end TreeSummary
end GraphQL
