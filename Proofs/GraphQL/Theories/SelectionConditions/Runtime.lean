import GraphQL.Theories.SelectionConditions
import Proofs.GraphQL.Execution.FieldGroups

/-! Runtime meaning of the shared Boolean/type conditions and flat extraction. -/

namespace GraphQL
namespace SelectionConditions

open Execution
open Execution.FieldGroups

theorem booleanConditionAllows_append (variableValues : VariableValues)
    (left right : List BooleanLiteral)
    : booleanConditionAllows variableValues (left ++ right)
      = (booleanConditionAllows variableValues left
          && booleanConditionAllows variableValues right) := by
  induction left with
  | nil => rfl
  | cons literal rest ih =>
      simp [booleanConditionAllows, ih, Bool.and_assoc]

theorem literalsForDirective_some_allows
    (variableValues : VariableValues) (directive : DirectiveApplication)
    (literals : List BooleanLiteral)
    (hliterals : literalsForDirective directive = some literals)
    : directiveAllowsSelectionBool variableValues directive
      = booleanConditionAllows variableValues literals := by
  cases directive <;> rename_i argument <;> cases argument <;>
    simp [literalsForDirective] at hliterals
  case skip.boolean value =>
    cases value <;> simp at hliterals
    subst literals
    rfl
  case skip.variable =>
    subst literals
    simp [booleanConditionAllows, BooleanLiteral.allows,
      BooleanLiteral.toDirective]
  case include.boolean value =>
    cases value <;> simp at hliterals
    subst literals
    rfl
  case include.variable =>
    subst literals
    simp [booleanConditionAllows, BooleanLiteral.allows,
      BooleanLiteral.toDirective]
  all_goals { subst literals; rfl }

theorem literalsForDirective_none_not_allows
    (variableValues : VariableValues) (directive : DirectiveApplication)
    (hliterals : literalsForDirective directive = none)
    : directiveAllowsSelectionBool variableValues directive = false := by
  cases directive <;> rename_i argument <;> cases argument <;>
    simp [literalsForDirective] at hliterals
  all_goals try {
    cases ‹Bool› <;>
      simp_all [directiveAllowsSelectionBool,
        inputValueBoolean?, InputValue.staticBoolean?] }
  all_goals
    try simp_all [directiveAllowsSelectionBool,
      inputValueBoolean?, InputValue.staticBoolean?]

theorem literalsForDirectives_some_allows (variableValues : VariableValues)
    : ∀ directives literals,
        literalsForDirectives directives = some literals
        -> selectionDirectivesAllowBool variableValues directives
            = booleanConditionAllows variableValues literals
  | [], literals, hliterals => by
      simp [literalsForDirectives] at hliterals
      subst literals
      rfl
  | directive :: rest, literals, hliterals => by
      simp only [literalsForDirectives] at hliterals
      cases hdirective : literalsForDirective directive with
      | none => simp [hdirective] at hliterals
      | some directiveLiterals =>
          cases hrest : literalsForDirectives rest with
          | none => simp [hdirective, hrest] at hliterals
          | some restLiterals =>
              simp [hdirective, hrest] at hliterals
              subst literals
              rw [show
                selectionDirectivesAllowBool variableValues (directive :: rest)
                  =
                    (directiveAllowsSelectionBool variableValues directive
                      && selectionDirectivesAllowBool variableValues rest) by
                  rfl]
              rw [literalsForDirective_some_allows variableValues directive
                directiveLiterals hdirective]
              rw [literalsForDirectives_some_allows variableValues rest
                restLiterals hrest]
              exact (booleanConditionAllows_append variableValues
                directiveLiterals restLiterals).symm

theorem literalsForDirectives_none_not_allows (variableValues : VariableValues)
    : ∀ directives,
        literalsForDirectives directives = none
        -> selectionDirectivesAllowBool variableValues directives = false
  | [], hliterals => by simp [literalsForDirectives] at hliterals
  | directive :: rest, hliterals => by
      simp only [literalsForDirectives] at hliterals
      cases hdirective : literalsForDirective directive with
      | none =>
          simp [hdirective] at hliterals
          simp [selectionDirectivesAllowBool,
            literalsForDirective_none_not_allows variableValues directive hdirective]
      | some directiveLiterals =>
          cases hrest : literalsForDirectives rest with
          | none =>
              simp [hdirective, hrest] at hliterals
              rw [show
                selectionDirectivesAllowBool variableValues (directive :: rest)
                  =
                    (directiveAllowsSelectionBool variableValues directive
                      && selectionDirectivesAllowBool variableValues rest) by
                  rfl]
              rw [literalsForDirectives_none_not_allows variableValues rest hrest]
              simp
          | some restLiterals =>
              simp [hdirective, hrest] at hliterals

theorem BooleanLiteral.allows_complement
    (variableValues : VariableValues) (literal : BooleanLiteral)
    : (literal.allows variableValues && literal.complement.allows variableValues)
      = false := by
  cases literal with
  | positive variableName =>
      simp only [BooleanLiteral.allows, BooleanLiteral.complement,
        BooleanLiteral.toDirective, directiveAllowsSelectionBool]
      cases hvalue :
        inputValueBoolean? variableValues (InputValue.variable variableName)
      · rfl
      · rename_i value
        cases value <;> rfl
  | negative variableName =>
      simp only [BooleanLiteral.allows, BooleanLiteral.complement,
        BooleanLiteral.toDirective, directiveAllowsSelectionBool]
      cases hvalue :
        inputValueBoolean? variableValues (InputValue.variable variableName)
      · rfl
      · rename_i value
        cases value <;> rfl

theorem insertBooleanLiteral_some_allows
    (variableValues : VariableValues) (literal : BooleanLiteral)
    : ∀ source target,
        insertBooleanLiteral literal source = some target
        -> booleanConditionAllows variableValues target
            = (literal.allows variableValues
                && booleanConditionAllows variableValues source)
  | [], target, hinsert => by
      simp [insertBooleanLiteral] at hinsert
      subst target
      simp [booleanConditionAllows]
  | candidate :: rest, target, hinsert => by
      simp only [insertBooleanLiteral] at hinsert
      split at hinsert
      · rename_i hequal
        simp at hinsert
        subst target
        have hliteral : literal = candidate := beq_iff_eq.mp hequal
        subst literal
        simp [booleanConditionAllows]
      · split at hinsert
        · simp at hinsert
        · split at hinsert
          · simp at hinsert
            subst target
            simp [booleanConditionAllows]
          · cases hrest : insertBooleanLiteral literal rest with
            | none => simp [hrest] at hinsert
            | some inserted =>
                simp [hrest] at hinsert
                subst target
                simp only [booleanConditionAllows]
                rw [insertBooleanLiteral_some_allows variableValues literal rest
                  inserted hrest]
                ac_rfl

theorem insertBooleanLiteral_none_not_allows
    (variableValues : VariableValues) (literal : BooleanLiteral)
    : ∀ source,
        insertBooleanLiteral literal source = none
        -> (literal.allows variableValues && booleanConditionAllows variableValues source)
            = false
  | [], hinsert => by simp [insertBooleanLiteral] at hinsert
  | candidate :: rest, hinsert => by
      simp only [insertBooleanLiteral] at hinsert
      split at hinsert
      · simp at hinsert
      · split at hinsert
        · rename_i hcomplement
          have hequal : literal.complement = candidate :=
            beq_iff_eq.mp hcomplement
          subst candidate
          change
            (literal.allows variableValues
              && (literal.complement.allows variableValues
                && booleanConditionAllows variableValues rest)) = false
          rw [← Bool.and_assoc, BooleanLiteral.allows_complement]
          rfl
        · split at hinsert
          · simp at hinsert
          · cases hrest : insertBooleanLiteral literal rest with
            | none =>
                simp [hrest] at hinsert
                have hfalse :=
                  insertBooleanLiteral_none_not_allows variableValues literal rest
                    hrest
                change
                  (literal.allows variableValues
                    && (candidate.allows variableValues
                      && booleanConditionAllows variableValues rest)) = false
                cases hliteral : literal.allows variableValues <;>
                  cases hcandidate : candidate.allows variableValues <;>
                  simp [hliteral] at hfalse ⊢
                exact hfalse
            | some inserted => simp [hrest] at hinsert

theorem canonicalBooleanCondition_some_allows (variableValues : VariableValues)
    : ∀ source target,
        canonicalBooleanCondition source = some target
        -> booleanConditionAllows variableValues source
            = booleanConditionAllows variableValues target
  | [], target, hcanonical => by
      simp [canonicalBooleanCondition] at hcanonical
      subst target
      rfl
  | literal :: rest, target, hcanonical => by
      simp only [canonicalBooleanCondition] at hcanonical
      cases hrest : canonicalBooleanCondition rest with
      | none => simp [hrest] at hcanonical
      | some restCondition =>
          cases hinsert : insertBooleanLiteral literal restCondition with
          | none => simp [hrest, hinsert] at hcanonical
          | some condition =>
              simp [hrest, hinsert] at hcanonical
              subst target
              rw [insertBooleanLiteral_some_allows variableValues literal
                restCondition condition hinsert]
              rw [← canonicalBooleanCondition_some_allows variableValues rest
                restCondition hrest]
              simp [booleanConditionAllows]

theorem canonicalBooleanCondition_none_not_allows (variableValues : VariableValues)
    : ∀ source,
        canonicalBooleanCondition source = none
        -> booleanConditionAllows variableValues source = false
  | [], hcanonical => by simp [canonicalBooleanCondition] at hcanonical
  | literal :: rest, hcanonical => by
      simp only [canonicalBooleanCondition] at hcanonical
      cases hrest : canonicalBooleanCondition rest with
      | none =>
          simp [hrest] at hcanonical
          have hfalse :=
            canonicalBooleanCondition_none_not_allows variableValues rest hrest
          change
            (literal.allows variableValues
              && booleanConditionAllows variableValues rest) = false
          rw [hfalse]
          simp
      | some restCondition =>
          cases hinsert : insertBooleanLiteral literal restCondition with
          | none =>
              simp [hrest, hinsert] at hcanonical
              have hfalse :=
                insertBooleanLiteral_none_not_allows variableValues literal
                  restCondition hinsert
              change
                (literal.allows variableValues
                  && booleanConditionAllows variableValues rest) = false
              rw [canonicalBooleanCondition_some_allows variableValues rest
                restCondition hrest]
              exact hfalse
          | some condition => simp [hrest, hinsert] at hcanonical

theorem contains_intersectPossibleTypes (runtimeType : Name) (left right : List Name)
    : (intersectPossibleTypes left right).contains runtimeType
      = (left.contains runtimeType && right.contains runtimeType) := by
  simp [intersectPossibleTypes]

theorem booleanConditionAllows_member
    (variableValues : VariableValues) (condition : List BooleanLiteral)
    (hallows : booleanConditionAllows variableValues condition = true)
    {literal : BooleanLiteral} (hmember : literal ∈ condition)
    : literal.allows variableValues = true := by
  induction condition with
  | nil => simp at hmember
  | cons head rest ih =>
      simp only [booleanConditionAllows, Bool.and_eq_true] at hallows
      simp only [List.mem_cons] at hmember
      exact hmember.elim
        (fun hequal => by simpa [hequal] using hallows.1)
        (fun hrest => ih hallows.2 hrest)

theorem booleanConditionAllows_filter_not_contains
    (variableValues : VariableValues)
    (inherited condition : List BooleanLiteral)
    (hinherited : booleanConditionAllows variableValues inherited = true)
    : booleanConditionAllows variableValues
        (condition.filter fun literal => !inherited.contains literal)
      = booleanConditionAllows variableValues condition := by
  induction condition with
  | nil => rfl
  | cons literal rest ih =>
      by_cases hcontains : inherited.contains literal = true
      · have hliteral :
            literal.allows variableValues = true :=
          booleanConditionAllows_member variableValues inherited hinherited
            (List.contains_iff_mem.mp hcontains)
        rw [List.filter_cons]
        simp only [hcontains, Bool.not_true, Bool.false_eq_true, if_false, ih,
          hliteral, booleanConditionAllows, Bool.true_and]
      · have hcontainsFalse : inherited.contains literal = false := by
          cases hvalue : inherited.contains literal with
          | false => rfl
          | true => contradiction
        rw [List.filter_cons]
        simp only [hcontainsFalse, Bool.not_false, if_true, ih,
          booleanConditionAllows]

def conditionOptionAllows (variableValues : VariableValues) (runtimeType : Name)
    : Option Condition -> Bool
  | none => false
  | some condition => condition.allows variableValues runtimeType

theorem conditionForBranch?_runtime
    (schema : Schema) (variableValues : VariableValues) (runtimeType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (start : Condition) (branch : BranchCondition)
    (hinherited : booleanConditionAllows variableValues inheritedBooleanCondition = true)
    : conditionOptionAllows variableValues runtimeType
        (conditionForBranch? schema inheritedBooleanCondition start branch)
      = (start.allows variableValues runtimeType
          && branch.allows schema variableValues runtimeType) := by
  cases branch with
  | typeCondition typeName =>
      unfold conditionForBranch?
      by_cases hempty :
          (intersectPossibleTypes start.possibleTypes
            (schema.getPossibleTypes typeName)).isEmpty = true
      · simp only [hempty, if_true, conditionOptionAllows,
          BranchCondition.allows, Condition.allows]
        have hcontains :
            (intersectPossibleTypes start.possibleTypes
              (schema.getPossibleTypes typeName)).contains runtimeType = false := by
          have hnil :
              intersectPossibleTypes start.possibleTypes
                  (schema.getPossibleTypes typeName)
                = [] := by
            simpa using hempty
          simp [hnil]
        rw [contains_intersectPossibleTypes] at hcontains
        unfold Schema.typeIncludesObjectBool
        cases hleft : start.possibleTypes.contains runtimeType <;>
          cases hright :
              (schema.getPossibleTypes typeName).contains runtimeType <;>
          simp_all
      · simp only [hempty, Bool.false_eq_true, if_false, conditionOptionAllows,
          BranchCondition.allows, Condition.allows]
        rw [contains_intersectPossibleTypes]
        unfold Schema.typeIncludesObjectBool
        ac_rfl
  | booleanLiteral literal =>
      simp only [conditionForBranch?]
      cases hcandidate
            : canonicalBooleanCondition (start.booleanCondition ++ [literal]) with
      | none =>
          simp only [conditionOptionAllows,
            BranchCondition.allows, Condition.allows]
          have hfalse :=
            canonicalBooleanCondition_none_not_allows variableValues
              (start.booleanCondition ++ [literal]) hcandidate
          rw [booleanConditionAllows_append] at hfalse
          simp [booleanConditionAllows] at hfalse
          cases hpossible : start.possibleTypes.contains runtimeType <;>
            cases hstart :
              booleanConditionAllows variableValues start.booleanCondition <;>
            cases hliteral : literal.allows variableValues <;>
            simp_all
      | some candidate =>
          let filtered :=
            candidate.filter
              fun item => !inheritedBooleanCondition.contains item
          change
            conditionOptionAllows variableValues runtimeType
                (do
                  let _globalBooleanCondition ←
                    canonicalBooleanCondition
                      (inheritedBooleanCondition ++ filtered)
                  some { start with booleanCondition := filtered })
              =
                (start.allows variableValues runtimeType
                  && (BranchCondition.booleanLiteral literal).allows schema
                    variableValues runtimeType)
          cases hglobal
                : canonicalBooleanCondition (inheritedBooleanCondition ++ filtered) with
          | none =>
              change
                false =
                  (start.possibleTypes.contains runtimeType
                    && booleanConditionAllows variableValues
                      start.booleanCondition
                    && literal.allows variableValues)
              have hfalse :=
                canonicalBooleanCondition_none_not_allows variableValues
                  (inheritedBooleanCondition ++ filtered) hglobal
              rw [booleanConditionAllows_append, hinherited,
                Bool.true_and] at hfalse
              rw [booleanConditionAllows_filter_not_contains variableValues
                inheritedBooleanCondition candidate hinherited] at hfalse
              have hcandidateAllows :=
                canonicalBooleanCondition_some_allows variableValues
                  (start.booleanCondition ++ [literal]) candidate hcandidate
              rw [booleanConditionAllows_append] at hcandidateAllows
              simp [booleanConditionAllows] at hcandidateAllows
              rw [← hcandidateAllows] at hfalse
              cases hpossible : start.possibleTypes.contains runtimeType <;>
                cases hstart :
                  booleanConditionAllows variableValues start.booleanCondition <;>
                cases hliteral : literal.allows variableValues <;>
                simp_all
          | some global =>
              change (start.possibleTypes.contains runtimeType
                        && booleanConditionAllows variableValues filtered)
                      = (start.possibleTypes.contains runtimeType
                          && booleanConditionAllows variableValues start.booleanCondition
                          && literal.allows variableValues)
              rw [booleanConditionAllows_filter_not_contains variableValues
                inheritedBooleanCondition candidate hinherited]
              rw [← canonicalBooleanCondition_some_allows variableValues
                (start.booleanCondition ++ [literal]) candidate hcandidate]
              rw [booleanConditionAllows_append]
              simp [booleanConditionAllows]
              ac_rfl

theorem conditionForBranches?_runtime
    (schema : Schema) (variableValues : VariableValues) (runtimeType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (start : Condition) (branches : List BranchCondition)
    (hinherited : booleanConditionAllows variableValues inheritedBooleanCondition = true)
    : conditionOptionAllows variableValues runtimeType
        (conditionForBranches? schema inheritedBooleanCondition start branches)
      = (start.allows variableValues runtimeType
          && branchConditionsAllow schema variableValues runtimeType branches) := by
  induction branches generalizing start with
  | nil =>
      simp [conditionForBranches?, conditionOptionAllows, branchConditionsAllow]
  | cons branch rest ih =>
      simp only [conditionForBranches?]
      cases hnext : conditionForBranch? schema inheritedBooleanCondition start branch with
      | none =>
          have hbranch :=
            conditionForBranch?_runtime schema variableValues runtimeType
              inheritedBooleanCondition start branch hinherited
          rw [hnext] at hbranch
          simp only [conditionOptionAllows] at hbranch
          simp only [conditionOptionAllows, branchConditionsAllow]
          rw [← Bool.and_assoc, ← hbranch]
          rfl
      | some next =>
          have hbranch :=
            conditionForBranch?_runtime schema variableValues runtimeType
              inheritedBooleanCondition start branch hinherited
          rw [hnext] at hbranch
          simp only [conditionOptionAllows] at hbranch
          change
            conditionOptionAllows variableValues runtimeType
                (conditionForBranches? schema inheritedBooleanCondition next rest)
              =
                (start.allows variableValues runtimeType
                  && branchConditionsAllow schema variableValues runtimeType
                    (branch :: rest))
          rw [ih next]
          rw [hbranch]
          simp [branchConditionsAllow, Bool.and_assoc]

theorem branchConditionsAllow_booleanLiterals
    (schema : Schema) (variableValues : VariableValues) (runtimeType : Name)
    (literals : List BooleanLiteral)
    : branchConditionsAllow schema variableValues runtimeType
        (literals.map BranchCondition.booleanLiteral)
      = booleanConditionAllows variableValues literals := by
  induction literals with
  | nil => rfl
  | cons literal rest ih =>
      simp [branchConditionsAllow, booleanConditionAllows,
        BranchCondition.allows, ih]

theorem branchConditionsForDirectives?_runtime
    (schema : Schema) (variableValues : VariableValues) (runtimeType : Name)
    (directives : List DirectiveApplication) (branches : List BranchCondition)
    (hbranches : branchConditionsForDirectives? directives = some branches)
    : branchConditionsAllow schema variableValues runtimeType branches
      = selectionDirectivesAllowBool variableValues directives := by
  cases hliterals : literalsForDirectives directives with
  | none =>
      simp [branchConditionsForDirectives?, hliterals] at hbranches
  | some literals =>
      have hallows :=
        literalsForDirectives_some_allows variableValues directives literals hliterals
      simp [branchConditionsForDirectives?, hliterals] at hbranches
      subst branches
      simpa [branchConditionsAllow_booleanLiterals] using hallows.symm

theorem branchConditionsForDirectives?_none_not_allows
    (variableValues : VariableValues) (directives : List DirectiveApplication)
    (hbranches : branchConditionsForDirectives? directives = none)
    : selectionDirectivesAllowBool variableValues directives = false := by
  cases hliterals : literalsForDirectives directives with
  | none =>
      exact literalsForDirectives_none_not_allows variableValues directives hliterals
  | some literals =>
      simp [branchConditionsForDirectives?, hliterals] at hbranches

def inlineFragmentTypeAllows (schema : Schema) (runtimeType : Name) : Option Name -> Bool
  | none => true
  | some typeName => schema.typeIncludesObjectBool typeName runtimeType

theorem branchConditionsForInlineFragment?_runtime
    (schema : Schema) (variableValues : VariableValues) (runtimeType : Name)
    (typeCondition : Option Name) (directives : List DirectiveApplication)
    (branches : List BranchCondition)
    (hbranches
      : branchConditionsForInlineFragment? typeCondition directives = some branches)
    : branchConditionsAllow schema variableValues runtimeType branches
      = (selectionDirectivesAllowBool variableValues directives
          && inlineFragmentTypeAllows schema runtimeType typeCondition) := by
  cases hboolean : branchConditionsForDirectives? directives with
  | none =>
      simp [branchConditionsForInlineFragment?, hboolean] at hbranches
  | some booleanBranches =>
      have hbooleanAllows :=
        branchConditionsForDirectives?_runtime schema variableValues runtimeType
          directives booleanBranches hboolean
      cases typeCondition with
      | none =>
          simp [branchConditionsForInlineFragment?, hboolean] at hbranches
          subst branches
          simpa [inlineFragmentTypeAllows] using hbooleanAllows
      | some typeName =>
          simp [branchConditionsForInlineFragment?, hboolean] at hbranches
          subst branches
          simp [branchConditionsAllow, BranchCondition.allows,
            inlineFragmentTypeAllows, hbooleanAllows, Bool.and_comm]

theorem doesFragmentTypeApplyBool_object
    {ObjectRef : Type} (schema : Schema) (executionParentType runtimeType : Name)
    (ref : ObjectRef) (typeCondition : Name)
    : doesFragmentTypeApplyBool schema executionParentType
        (.object runtimeType ref) typeCondition
      = schema.typeIncludesObjectBool typeCondition runtimeType := by
  rfl

theorem collectFlatSelection_inlineFragment_object
    {ObjectRef : Type}
    (schema : Schema) (variableValues : VariableValues)
    (executionParentType runtimeType : Name) (ref : ObjectRef)
    (typeCondition : Option Name) (directives : List DirectiveApplication)
    (selectionSet : List Selection)
    : collectFlatSelection schema variableValues executionParentType
        (.object runtimeType ref)
        (.inlineFragment typeCondition directives selectionSet)
      = if selectionDirectivesAllowBool variableValues directives
            && inlineFragmentTypeAllows schema runtimeType typeCondition then
          collectFlatFields schema variableValues executionParentType
            (.object runtimeType ref) selectionSet
        else
          [] := by
  cases typeCondition <;>
    simp [collectFlatSelection, inlineFragmentTypeAllows,
      doesFragmentTypeApplyBool_object]

theorem runtimeFields_append
    (variableValues : VariableValues) (executionParentType runtimeType : Name)
    (left right : List ConditionedField)
    : runtimeFields variableValues executionParentType runtimeType (left ++ right)
      = runtimeFields variableValues executionParentType runtimeType left
        ++ runtimeFields variableValues executionParentType runtimeType right := by
  simp [runtimeFields]

theorem runtimeFields_singleton
    (variableValues : VariableValues) (executionParentType runtimeType : Name)
    (condition : Condition) (field : Field)
    : runtimeFields variableValues executionParentType runtimeType [{ condition, field }]
      = if condition.allows variableValues runtimeType then
          [{
            parentType := executionParentType
            responseName := field.responseName
            fieldName := field.fieldName
            arguments := field.arguments
            selectionSet := field.selectionSet
          }]
        else
          [] := by
  simp [runtimeFields]

theorem extractFields_runtimeFields
    {ObjectRef : Type}
    (schema : Schema) (variableValues : VariableValues)
    (executionParentType runtimeType : Name) (ref : ObjectRef)
    (inheritedBooleanCondition : List BooleanLiteral)
    (currentCondition : Condition) (selectionSet : List Selection)
    (hinherited : booleanConditionAllows variableValues inheritedBooleanCondition = true)
    : runtimeFields variableValues executionParentType runtimeType
        (extractFields schema inheritedBooleanCondition currentCondition selectionSet)
      = if currentCondition.allows variableValues runtimeType then
          collectFlatFields schema variableValues executionParentType
            (.object runtimeType ref) selectionSet
        else
          [] := by
  cases hselectionSet : selectionSet with
  | nil =>
      subst selectionSet
      simp [extractFields, runtimeFields, collectFlatFields]
  | cons selection rest =>
      subst selectionSet
      cases hselection : selection with
      | field responseName fieldName arguments directives childSelectionSet =>
          subst selection
          rw [extractFields, collectFlatFields]
          have ihRest :=
            extractFields_runtimeFields schema variableValues executionParentType
              runtimeType ref inheritedBooleanCondition currentCondition rest hinherited
          cases hbranches : branchConditionsForDirectives? directives with
          | none =>
              have hdirectives :=
                branchConditionsForDirectives?_none_not_allows variableValues
                  directives hbranches
              simp only [List.nil_append]
              rw [ihRest]
              cases hcurrent : currentCondition.allows variableValues runtimeType <;>
                simp [hdirectives, collectFlatSelection]
          | some nextBranches =>
              have hbranchesAllow :=
                branchConditionsForDirectives?_runtime schema variableValues
                  runtimeType directives nextBranches hbranches
              cases hnext
                    : conditionForBranches? schema inheritedBooleanCondition
                        currentCondition nextBranches with
              | none =>
                  have hnextAllows :=
                    conditionForBranches?_runtime schema variableValues runtimeType
                      inheritedBooleanCondition currentCondition nextBranches hinherited
                  rw [hnext] at hnextAllows
                  simp only [conditionOptionAllows] at hnextAllows
                  rw [hbranchesAllow] at hnextAllows
                  simp only [hnext, List.nil_append]
                  rw [ihRest]
                  have hgateFalse :
                      (currentCondition.allows variableValues runtimeType
                        && selectionDirectivesAllowBool variableValues directives)
                        = false :=
                    hnextAllows.symm
                  cases hcurrent : currentCondition.allows variableValues runtimeType <;>
                    cases hdirectives :
                      selectionDirectivesAllowBool variableValues directives
                  all_goals
                    simp [hcurrent, hdirectives, collectFlatSelection]
                      at hgateFalse ⊢
              | some nextCondition =>
                  have hnextAllows :=
                    conditionForBranches?_runtime schema variableValues runtimeType
                      inheritedBooleanCondition currentCondition nextBranches hinherited
                  rw [hnext] at hnextAllows
                  simp only [conditionOptionAllows] at hnextAllows
                  rw [hbranchesAllow] at hnextAllows
                  simp only [hnext]
                  rw [runtimeFields_append, runtimeFields_singleton, ihRest]
                  rw [hnextAllows]
                  cases hcurrent : currentCondition.allows variableValues runtimeType <;>
                    cases hdirectives :
                      selectionDirectivesAllowBool variableValues directives
                  all_goals
                    simp [hdirectives, collectFlatSelection]
      | inlineFragment typeCondition directives childSelectionSet =>
          subst selection
          rw [extractFields, collectFlatFields]
          have ihRest :=
            extractFields_runtimeFields schema variableValues executionParentType
              runtimeType ref inheritedBooleanCondition currentCondition rest hinherited
          cases hbranches
                : branchConditionsForInlineFragment? typeCondition directives with
          | none =>
              have hboolean : branchConditionsForDirectives? directives = none := by
                cases hcandidate : branchConditionsForDirectives? directives with
                | none => rfl
                | some booleanBranches =>
                    simp [branchConditionsForInlineFragment?, hcandidate] at hbranches
              have hdirectives :=
                branchConditionsForDirectives?_none_not_allows variableValues
                  directives hboolean
              simp only [List.nil_append]
              rw [ihRest]
              rw [collectFlatSelection_inlineFragment_object]
              simp [hdirectives]
          | some nextBranches =>
              have hbranchesAllow :=
                branchConditionsForInlineFragment?_runtime schema variableValues
                  runtimeType typeCondition directives nextBranches hbranches
              cases hnext
                    : conditionForBranches? schema inheritedBooleanCondition
                        currentCondition nextBranches with
              | none =>
                  have hnextAllows :=
                    conditionForBranches?_runtime schema variableValues runtimeType
                      inheritedBooleanCondition currentCondition nextBranches hinherited
                  rw [hnext] at hnextAllows
                  simp only [conditionOptionAllows] at hnextAllows
                  rw [hbranchesAllow] at hnextAllows
                  simp only [hnext, List.nil_append]
                  rw [ihRest]
                  rw [collectFlatSelection_inlineFragment_object]
                  have hgateFalse :
                      (currentCondition.allows variableValues runtimeType
                        && (selectionDirectivesAllowBool variableValues directives
                          && inlineFragmentTypeAllows schema runtimeType
                            typeCondition))
                        = false :=
                    hnextAllows.symm
                  cases hcurrent : currentCondition.allows variableValues runtimeType <;>
                    cases hfragment :
                      (selectionDirectivesAllowBool variableValues directives
                        && inlineFragmentTypeAllows schema runtimeType typeCondition)
                  all_goals
                    simp only [hcurrent, hfragment, Bool.false_eq_true,
                      Bool.true_eq_false, Bool.false_and, Bool.true_and,
                      if_false, if_true, List.nil_append] at hgateFalse ⊢
              | some nextCondition =>
                  have hnextAllows :=
                    conditionForBranches?_runtime schema variableValues runtimeType
                      inheritedBooleanCondition currentCondition nextBranches hinherited
                  rw [hnext] at hnextAllows
                  simp only [conditionOptionAllows] at hnextAllows
                  rw [hbranchesAllow] at hnextAllows
                  have ihChild :=
                    extractFields_runtimeFields schema variableValues
                      executionParentType runtimeType ref inheritedBooleanCondition
                      nextCondition childSelectionSet hinherited
                  simp only [hnext]
                  rw [runtimeFields_append, ihChild, ihRest]
                  rw [collectFlatSelection_inlineFragment_object]
                  rw [hnextAllows]
                  cases hcurrent : currentCondition.allows variableValues runtimeType <;>
                    cases hfragment :
                      (selectionDirectivesAllowBool variableValues directives
                        && inlineFragmentTypeAllows schema runtimeType typeCondition)
                  all_goals
                    simp only [Bool.false_eq_true, Bool.false_and, Bool.true_and,
                      if_false, if_true, List.nil_append]
termination_by SelectionSet.size selectionSet
decreasing_by
  all_goals
    try subst selectionSet
    try subst selection
    simp_wf
    simp_all [SelectionSet.size, Selection.size]
    omega

end SelectionConditions
end GraphQL
